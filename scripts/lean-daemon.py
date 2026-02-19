#!/usr/bin/env python3
"""Persistent Lean language server daemon for fast incremental checking.

Architecture:
  - Starts `lake serve` as a subprocess and communicates via LSP (JSON-RPC)
  - Listens on a Unix domain socket for check requests
  - When a file is checked, sends textDocument/didOpen or didChange to the server
  - Waits for full file processing (via $/lean/fileProgress) before returning
  - Collects all diagnostics and returns them to the client

Staleness:
  `lake serve` resolves the module dependency graph at startup. When .lean files
  are added, deleted, or moved, the running server can't resolve new module names,
  causing indefinite hangs. To handle this, we snapshot the set of .lean files at
  startup and compare before each check. If the file set changed, we automatically
  restart `lake serve`. After a restart, the first check of each file is slow
  (cold start, ~20-90s) as dependencies are re-elaborated.

Usage:
  # Start daemon (blocks, run in background):
  python3 scripts/lean-daemon.py &

  # Check a file (from scripts/lean-check):
  scripts/lean-check AKS/Graph/Regular.lean
"""

import json
import os
import socket
import subprocess
import sys
import threading
import time

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# Derive unique paths from project root so multiple daemons can coexist
import hashlib
_project_hash = hashlib.md5(PROJECT_ROOT.encode()).hexdigest()[:8]
SOCKET_PATH = f"/tmp/lean-daemon-{_project_hash}.sock"


class LspConnection:
    """Low-level LSP JSON-RPC connection over stdin/stdout."""

    def __init__(self, proc: subprocess.Popen):
        self.proc = proc
        self.stdin = proc.stdin
        self.stdout = proc.stdout
        self._lock = threading.Lock()
        self._next_id = 1
        self._pending: dict[int, threading.Event] = {}
        self._results: dict[int, dict] = {}
        # Diagnostics: accumulate all diagnostics per URI
        self._diagnostics: dict[str, list] = {}
        # Completion tracking: require BOTH fileProgress:[] AND publishDiagnostics
        # before signaling completion. The Lean server can send fileProgress:[]
        # before publishDiagnostics in the same batch (especially for fast changes),
        # so waiting only for fileProgress:[] returns before diagnostics are stored.
        self._progress_done: dict[str, bool] = {}
        self._diagnostics_received: dict[str, bool] = {}
        self._file_done_events: dict[str, threading.Event] = {}
        self._reader_thread = threading.Thread(target=self._reader, daemon=True)
        self._reader_thread.start()

    def _read_message(self) -> dict | None:
        """Read one LSP message from stdout."""
        headers = {}
        while True:
            line = self.stdout.readline()
            if not line:
                return None
            line = line.decode("utf-8").strip()
            if line == "":
                break
            if ": " in line:
                key, val = line.split(": ", 1)
                headers[key] = val
        length = int(headers.get("Content-Length", 0))
        if length == 0:
            return None
        body = self.stdout.read(length)
        return json.loads(body.decode("utf-8"))

    def _reader(self):
        """Background thread reading messages from the server."""
        while True:
            msg = self._read_message()
            if msg is None:
                break

            # Handle responses to our requests
            if "id" in msg and msg["id"] in self._pending:
                rid = msg["id"]
                self._results[rid] = msg
                self._pending[rid].set()

            # Handle publishDiagnostics — accumulate (server may send multiple)
            elif msg.get("method") == "textDocument/publishDiagnostics":
                uri = msg["params"]["uri"]
                self._diagnostics[uri] = msg["params"]["diagnostics"]
                # Mark that we have diagnostics; trigger if progress also done
                self._diagnostics_received[uri] = True
                if self._progress_done.get(uri, False):
                    if uri in self._file_done_events:
                        self._file_done_events[uri].set()

            # Handle $/lean/fileProgress — track when file is fully processed
            elif msg.get("method") == "$/lean/fileProgress":
                uri = msg["params"]["textDocument"]["uri"]
                processing = msg["params"].get("processing", [])
                if not processing:
                    # Mark progress done; trigger if diagnostics also received
                    self._progress_done[uri] = True
                    if self._diagnostics_received.get(uri, False):
                        if uri in self._file_done_events:
                            self._file_done_events[uri].set()

    def _send(self, obj: dict):
        """Send a JSON-RPC message."""
        body = json.dumps(obj).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("utf-8")
        with self._lock:
            self.stdin.write(header + body)
            self.stdin.flush()

    def request(self, method: str, params: dict, timeout: float = 60) -> dict:
        """Send a request and wait for response."""
        with self._lock:
            rid = self._next_id
            self._next_id += 1
        event = threading.Event()
        self._pending[rid] = event
        self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        if not event.wait(timeout):
            raise TimeoutError(f"LSP request {method} timed out after {timeout}s")
        return self._results.pop(rid)

    def notify(self, method: str, params: dict):
        """Send a notification (no response expected)."""
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def prepare_wait(self, uri: str):
        """Reset wait state for a URI. Must be called BEFORE sending
        didOpen/didChange to avoid a race where the server sends
        fileProgress:[] before publishDiagnostics in the same batch.

        Requires BOTH fileProgress:[] AND publishDiagnostics to arrive
        before signaling completion, ensuring diagnostics are populated."""
        self._progress_done[uri] = False
        self._diagnostics_received[uri] = False
        event = threading.Event()
        self._file_done_events[uri] = event
        # Clear stale diagnostics so we don't return old results
        self._diagnostics.pop(uri, None)

    def wait_file_done(self, uri: str, timeout: float = 120) -> list:
        """Wait for a file to be fully processed, then return diagnostics.

        prepare_wait(uri) must have been called before the notification
        that triggers processing."""
        event = self._file_done_events.get(uri)
        if event is None:
            raise RuntimeError(f"prepare_wait was not called for {uri}")

        if not event.wait(timeout):
            raise TimeoutError(
                f"File processing for {uri} timed out after {timeout}s"
            )
        self._file_done_events.pop(uri, None)
        return self._diagnostics.get(uri, [])


def _snapshot_lean_files() -> frozenset[str]:
    """Return the set of project .lean file paths relative to PROJECT_ROOT.

    Includes top-level .lean files and everything under AKS/.
    Excludes .lake/ (Mathlib, dependencies)."""
    import glob
    files: set[str] = set()
    for pattern in ["*.lean", "AKS/**/*.lean"]:
        files.update(glob.glob(pattern, root_dir=PROJECT_ROOT, recursive=True))
    return frozenset(files)


class LeanDaemon:
    """Persistent Lean language server wrapper."""

    def __init__(self):
        self.conn: LspConnection | None = None
        self.opened_files: dict[str, int] = {}  # uri -> version
        self._file_snapshot: frozenset[str] = frozenset()

    def start(self):
        """Start lake serve and initialize LSP."""
        # Ensure CertCheck shared lib is built before starting LSP.
        # Lake needs it for modules that import CertCheck (precompileModules).
        print(f"[lean-daemon] Building CertCheck shared lib...", flush=True)
        subprocess.run(
            ["lake", "build", "CertCheck:shared"],
            cwd=PROJECT_ROOT,
            capture_output=True,
        )
        # Pass --plugin to the LSP server so workers get precompiled CertCheck
        # code for fast native_decide. Two Lake/Lean bugs make this necessary:
        # 1. Lake classifies single-root precompiled libs as "plugins" which
        #    LSP workers ignore (they only load "dynlibs" from setup-file JSON)
        # 2. --load-dynlib forwarding is broken: the server forwards it as
        #    -l<path> but 'l' is missing from the C++ getopt option string,
        #    so workers reject it. --plugin forwards as -p<path> which works.
        certcheck_lib = os.path.join(
            PROJECT_ROOT, ".lake", "build", "lib", "libaks_CertCheck.so")
        serve_args = ["lake", "serve", "--",
                      f"--plugin={certcheck_lib}"]
        print(f"[lean-daemon] Starting lake serve in {PROJECT_ROOT}...", flush=True)
        proc = subprocess.Popen(
            serve_args,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=PROJECT_ROOT,
        )
        self.conn = LspConnection(proc)

        # Initialize
        t0 = time.time()
        self.conn.request("initialize", {
            "processId": os.getpid(),
            "rootUri": f"file://{PROJECT_ROOT}",
            "capabilities": {
                "textDocument": {
                    "publishDiagnostics": {"relatedInformation": True}
                }
            },
        })
        self.conn.notify("initialized", {})
        self._file_snapshot = _snapshot_lean_files()
        dt = time.time() - t0
        print(f"[lean-daemon] Initialized in {dt:.1f}s", flush=True)

    def files_changed(self) -> bool:
        """Check if the set of .lean files has changed since startup."""
        return _snapshot_lean_files() != self._file_snapshot

    def check_file(self, filepath: str) -> dict:
        """Check a file and return diagnostics after full processing."""
        abspath = (
            os.path.join(PROJECT_ROOT, filepath)
            if not filepath.startswith("/")
            else filepath
        )
        uri = f"file://{abspath}"

        with open(abspath, "r") as f:
            content = f.read()

        t0 = time.time()

        # Prepare wait state BEFORE sending the notification.
        # Requires both fileProgress:[] and publishDiagnostics before
        # signaling completion, preventing the race where fileProgress:[]
        # arrives before diagnostics are stored.
        self.conn.prepare_wait(uri)

        if uri in self.opened_files:
            # File already open, send didChange
            self.opened_files[uri] += 1
            version = self.opened_files[uri]
            self.conn.notify("textDocument/didChange", {
                "textDocument": {"uri": uri, "version": version},
                "contentChanges": [{"text": content}],
            })
        else:
            # First time, send didOpen
            self.opened_files[uri] = 1
            self.conn.notify("textDocument/didOpen", {
                "textDocument": {
                    "uri": uri,
                    "languageId": "lean4",
                    "version": 1,
                    "text": content,
                },
            })

        # Wait for FULL file processing (not just first diagnostics)
        diagnostics = self.conn.wait_file_done(uri, timeout=120)
        dt = time.time() - t0

        return {
            "file": filepath,
            "time_seconds": round(dt, 2),
            "diagnostics": diagnostics,
        }

    def close_file(self, filepath: str):
        """Close a file to release its LSP worker process.

        The Lean LSP server spawns a separate --worker process per open file.
        Without closing, --all accumulates 50+ workers consuming 10+ GB RAM."""
        abspath = (
            os.path.join(PROJECT_ROOT, filepath)
            if not filepath.startswith("/")
            else filepath
        )
        uri = f"file://{abspath}"
        if uri in self.opened_files:
            self.conn.notify("textDocument/didClose", {
                "textDocument": {"uri": uri},
            })
            del self.opened_files[uri]

    def restart_if_stale(self) -> bool:
        """Restart lake serve if the set of .lean files has changed.

        Returns True if a restart occurred."""
        if not self.files_changed():
            return False
        print("[lean-daemon] File layout changed, restarting lake serve...", flush=True)
        self.shutdown()
        self.opened_files.clear()
        self.start()
        return True

    def shutdown(self):
        """Gracefully shut down the server."""
        if self.conn:
            try:
                self.conn.request("shutdown", {}, timeout=5)
                self.conn.notify("exit", {})
            except Exception:
                pass
            if self.conn.proc.poll() is None:
                self.conn.proc.terminate()


def run_daemon():
    """Main entry point: start daemon and listen on socket."""
    # Clean up stale socket
    if os.path.exists(SOCKET_PATH):
        os.unlink(SOCKET_PATH)

    daemon = LeanDaemon()
    daemon.start()
    restart_lock = threading.Lock()

    # Listen on Unix domain socket
    server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    server.bind(SOCKET_PATH)
    server.listen(5)
    print(f"[lean-daemon] Listening on {SOCKET_PATH}", flush=True)

    def handle_client(client: socket.socket):
        try:
            data = b""
            while True:
                chunk = client.recv(4096)
                if not chunk:
                    break
                data += chunk
                if b"\n" in data:
                    break
            request = json.loads(data.decode("utf-8"))

            if request.get("command") == "check":
                with restart_lock:
                    daemon.restart_if_stale()
                result = daemon.check_file(request["file"])
                # Close file after check if requested (saves memory in --all mode)
                if request.get("close_after"):
                    daemon.close_file(request["file"])
                response = json.dumps(result)
            elif request.get("command") == "close":
                daemon.close_file(request["file"])
                response = json.dumps({"status": "closed"})
            elif request.get("command") == "ping":
                response = json.dumps({"status": "ok"})
            elif request.get("command") == "shutdown":
                response = json.dumps({"status": "shutting_down"})
                client.sendall(response.encode("utf-8"))
                client.close()
                daemon.shutdown()
                server.close()
                os.unlink(SOCKET_PATH)
                sys.exit(0)
            else:
                response = json.dumps({"error": f"Unknown command: {request}"})

            client.sendall(response.encode("utf-8"))
        except Exception as e:
            try:
                client.sendall(json.dumps({"error": str(e)}).encode("utf-8"))
            except Exception:
                pass
        finally:
            client.close()

    try:
        while True:
            client, _ = server.accept()
            threading.Thread(
                target=handle_client, args=(client,), daemon=True
            ).start()
    except KeyboardInterrupt:
        pass
    finally:
        daemon.shutdown()
        server.close()
        if os.path.exists(SOCKET_PATH):
            os.unlink(SOCKET_PATH)


if __name__ == "__main__":
    run_daemon()
