#!/usr/bin/env -S cargo +nightly -Zscript
---cargo
[dependencies]
notify = "8"
serde_json = "1"
nix = { version = "0.29", features = ["signal", "process"] }

[profile.release]
opt-level = 2
---

//! Unified Lean MCP server: `snippet` (ad-hoc eval) + `check` (incremental LSP).
//!
//! Runs as an MCP server over stdio (newline-delimited JSON-RPC).
//! Keeps `lake serve` warm for fast incremental checking.
//!
//! Architecture:
//!   The MCP stdin reader sends commands to a coordinator thread via mpsc.
//!   The coordinator owns lake serve, the LSP reader, and the file watcher.
//!   Results are sent back via per-request response channels, then formatted
//!   as MCP tool results on stdout.
//!
//!   ```text
//!   MCP stdin reader  ──→ ┌─────────────┐ ──→ lake serve stdin
//!   LSP reader        ──→ │ Coordinator  │
//!   File watcher      ──→ │ (owns state) │ ──→ response channels ──→ MCP stdout
//!                         └─────────────┘
//!   ```

use notify::{Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use serde_json::Value;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{ChildStdin, ChildStdout, Command, Stdio};
use std::sync::mpsc::{self, Receiver, Sender, SyncSender};
use std::time::{Duration, Instant};
use std::{env, fs, process, thread};

/// A running `lake serve` process. Owns the stdin pipe, child PID, and
/// the LSP reader thread handle. On drop, kills the process group and joins
/// the reader thread, ensuring all messages from this incarnation are flushed
/// to the coordinator's channel before the drop completes.
struct ServeProcess {
    stdin: ChildStdin,
    child: std::process::Child,
    reader_handle: Option<thread::JoinHandle<()>>,
}

impl Drop for ServeProcess {
    fn drop(&mut self) {
        // Kill the entire process group (lake serve + lean --server).
        // This closes stdout, unblocking the reader thread.
        let pgid = nix::unistd::Pid::from_raw(self.child.id() as i32);
        let _ = nix::sys::signal::killpg(pgid, nix::sys::signal::Signal::SIGKILL);
        // Join the reader so any messages it sent are guaranteed in the channel.
        if let Some(h) = self.reader_handle.take() { let _ = h.join(); }
        // Reap the child (Child::wait calls waitpid, preventing zombies).
        let _ = self.child.wait();
    }
}

#[derive(Debug)]
enum LeanError {
    Io(io::Error),
    Json(serde_json::Error),
    Timeout { operation: &'static str, seconds: u64 },
    LspNotStarted,
    ServerRestarted,
    ServerInitializing,
}

impl fmt::Display for LeanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LeanError::Io(e) => write!(f, "I/O error: {e}"),
            LeanError::Json(e) => write!(f, "JSON error: {e}"),
            LeanError::Timeout { operation, seconds } =>
                write!(f, "{operation} timed out after {seconds}s"),
            LeanError::LspNotStarted => write!(f, "LSP not started"),
            LeanError::ServerRestarted => write!(f, "Server restarted"),
            LeanError::ServerInitializing => write!(f, "Server initializing"),
        }
    }
}

impl From<io::Error> for LeanError {
    fn from(e: io::Error) -> Self { LeanError::Io(e) }
}

impl From<serde_json::Error> for LeanError {
    fn from(e: serde_json::Error) -> Self { LeanError::Json(e) }
}

type Result<T> = std::result::Result<T, LeanError>;

enum Cmd {
    Check {
        file: String,
        close_after: bool,
        respond: SyncSender<Result<Value>>,
    },
    Restart {
        respond: SyncSender<Result<Value>>,
    },
    Shutdown {
        respond: SyncSender<()>,
    },
    /// LSP message from the reader thread
    LspMessage(Value),
    /// A .lean file was modified on disk
    FileChanged(String),
    /// A .lean file was created or deleted — restart lake serve
    LayoutChanged,
    /// LSP reader hit EOF — lake serve crashed
    LspCrashed,
}

struct PendingCheck {
    filepath: String,
    t0: Instant,
    close_after: bool,
    respond: SyncSender<Result<Value>>,
}

/// Per-file (per-URI) state tracked by the coordinator.
struct FileState {
    /// LSP document version.
    version: u64,
    /// When this file was last checked — for idle eviction.
    last_active: Instant,
    /// Latest diagnostics from the LSP.
    diagnostics: Vec<Value>,
    /// Whether `$/lean/fileProgress` reported processing complete.
    progress_done: bool,
    /// Whether `textDocument/publishDiagnostics` was received.
    diagnostics_received: bool,
    /// Pending check requests waiting for completion.
    pending_checks: Vec<PendingCheck>,
}

impl FileState {
    fn new_opened() -> Self {
        FileState {
            version: 1,
            last_active: Instant::now(),
            diagnostics: Vec::new(),
            progress_done: false,
            diagnostics_received: false,
            pending_checks: Vec::new(),
        }
    }

    /// Reset transient check state for a new check, preserving version.
    fn reset_check(&mut self) {
        let version = self.version;
        *self = FileState { version, ..FileState::new_opened() };
    }

    fn bump_version(&mut self) -> u64 {
        self.version += 1;
        self.version
    }
}

struct Coordinator {
    project_root: PathBuf,
    cmd_rx: Receiver<Cmd>,
    cmd_tx: Sender<Cmd>,
    ready_tx: Option<SyncSender<()>>,
    /// The running lake serve process. Dropping this kills the process and
    /// joins its reader thread, ensuring stale messages are flushed to cmd_rx.
    serve: Option<ServeProcess>,
    _watcher: Option<RecommendedWatcher>,
    next_lsp_id: u64,
    /// Per-file state, keyed by URI.
    files: HashMap<String, FileState>,
    /// Files changed on disk but not yet notified to the LSP.
    pending_changes: HashSet<String>,
    layout_changed: bool,
    max_concurrent: usize,
    active_count: usize,
    check_queue: VecDeque<PendingCheck>,
    shutting_down: bool,
}

impl Coordinator {
    fn new(
        project_root: PathBuf,
        cmd_rx: Receiver<Cmd>,
        cmd_tx: Sender<Cmd>,
        ready_tx: SyncSender<()>,
    ) -> Self {
        let max_concurrent = env::var("LEAN_DAEMON_JOBS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(|| {
                let cpus = thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4);
                cpus.min(8)
            });

        Coordinator {
            project_root,
            cmd_rx,
            cmd_tx,
            ready_tx: Some(ready_tx),
            serve: None,
            _watcher: None,
            next_lsp_id: 1,
            files: HashMap::new(),
            pending_changes: HashSet::new(),
            layout_changed: false,
            max_concurrent,
            active_count: 0,
            check_queue: VecDeque::new(),
            shutting_down: false,
        }
    }

    fn run(mut self) {
        self._watcher = start_watcher(&self.project_root, self.cmd_tx.clone());
        if self._watcher.is_some() {
            eprintln!("[lean] File watcher started (inotify)");
        } else {
            eprintln!("[lean] Warning: file watcher failed to start");
        }

        if let Err(e) = self.start_lake_serve() {
            eprintln!("[lean] Failed to start lake serve: {e}");
            process::exit(1);
        }

        if let Some(tx) = self.ready_tx.take() {
            let _ = tx.send(());
        }

        loop {
            match self.cmd_rx.recv_timeout(Duration::from_secs(60)) {
                Ok(cmd) => self.handle_cmd(cmd),
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    self.evict_idle_files();
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
            }
        }
    }

    fn handle_cmd(&mut self, cmd: Cmd) {
        match cmd {
            Cmd::Check { file, close_after, respond } => {
                self.restart_if_stale();
                if self.active_count < self.max_concurrent {
                    self.active_count += 1;
                    self.start_check(&file, close_after, respond);
                } else {
                    self.check_queue.push_back(PendingCheck {
                        filepath: file,
                        t0: Instant::now(),
                        close_after,
                        respond,
                    });
                }
            }
            Cmd::Restart { respond } => {
                eprintln!("[lean] Restart requested, killing lake serve...");
                self.drop_serve();
                if self.drain_stale_lsp_messages() { return; }
                match self.start_lake_serve() {
                    Ok(()) => {
                        let _ = respond.send(Ok(serde_json::json!({
                            "restarted": true,
                        })));
                    }
                    Err(e) => {
                        let _ = respond.send(Err(e));
                    }
                }
            }
            Cmd::Shutdown { respond } => {
                self.shutting_down = true;
                self.drop_serve();
                let _ = respond.send(());
                return;
            }
            Cmd::LspMessage(msg) => {
                self.handle_lsp_message(msg);
            }
            Cmd::FileChanged(relpath) => {
                self.pending_changes.insert(relpath);
            }
            Cmd::LayoutChanged => {
                self.layout_changed = true;
            }
            Cmd::LspCrashed => {
                if !self.shutting_down {
                    self.handle_lsp_crash();
                }
            }
        }
    }

    fn fail_all_pending(&mut self) {
        for fs in self.files.values_mut() {
            for check in fs.pending_checks.drain(..) {
                let _ = check.respond.send(Err(LeanError::ServerRestarted));
            }
        }
        for queued in self.check_queue.drain(..) {
            let _ = queued.respond.send(Err(LeanError::ServerRestarted));
        }
        self.active_count = 0;
    }

    fn debug_assert_active_count(&self) {
        debug_assert_eq!(
            self.active_count,
            self.files.values().filter(|fs| !fs.pending_checks.is_empty()).count(),
            "active_count desynced from actual pending checks",
        );
    }

    // -- Lake serve lifecycle -----------------------------------------------

    fn start_lake_serve(&mut self) -> Result<()> {
        eprintln!("[lean] Starting lake serve in {}...", self.project_root.display());
        let mut child = Command::new("lake")
            .args(["serve"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .current_dir(&self.project_root)
            .process_group(0)
            .spawn()?;

        let stdin = child.stdin.take().ok_or(LeanError::Io(io::Error::new(io::ErrorKind::Other, "No stdin")))?;
        let stdout = child.stdout.take().ok_or(LeanError::Io(io::Error::new(io::ErrorKind::Other, "No stdout")))?;

        self.next_lsp_id = 1;
        self.fail_all_pending();
        self.files.clear();
        self.pending_changes.clear();
        self.layout_changed = false;

        let tx = self.cmd_tx.clone();
        let reader_handle = thread::Builder::new()
            .name("lsp-reader".into())
            .spawn(move || lsp_reader_thread(tx, stdout))?;

        self.serve = Some(ServeProcess {
            stdin,
            child,
            reader_handle: Some(reader_handle),
        });

        // LSP initialize handshake
        let t0 = Instant::now();
        let init_id = self.next_lsp_id;
        self.next_lsp_id += 1;
        self.lsp_send_raw(&serde_json::to_vec(&serde_json::json!({
            "jsonrpc": "2.0",
            "id": init_id,
            "method": "initialize",
            "params": {
                "processId": process::id(),
                "rootUri": path_to_uri(&self.project_root),
                "capabilities": {
                    "textDocument": {
                        "publishDiagnostics": {"relatedInformation": true}
                    }
                },
            },
        }))?)?;

        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(LeanError::Timeout { operation: "initialize", seconds: 60 });
            }
            match self.cmd_rx.recv_timeout(remaining) {
                Ok(Cmd::LspMessage(msg)) => {
                    if msg.get("id").and_then(|v| v.as_u64()) == Some(init_id) {
                        break;
                    }
                    self.handle_lsp_message(msg);
                }
                Ok(Cmd::FileChanged(p)) => { self.pending_changes.insert(p); }
                Ok(Cmd::LayoutChanged) => { self.layout_changed = true; }
                Ok(Cmd::Check { respond, .. }) => {
                    let _ = respond.send(Err(LeanError::ServerInitializing));
                }
                Ok(Cmd::Restart { respond }) => {
                    let _ = respond.send(Err(LeanError::ServerInitializing));
                }
                Ok(Cmd::LspCrashed) => {}
                Ok(Cmd::Shutdown { respond }) => {
                    self.drop_serve();
                    let _ = respond.send(());
                    return Ok(());
                }
                Err(_) => return Err(LeanError::Timeout { operation: "initialize", seconds: 60 }),
            }
        }

        self.lsp_notify("initialized", serde_json::json!({}))?;
        eprintln!(
            "[lean] Initialized in {:.1}s (max {} concurrent checks)",
            t0.elapsed().as_secs_f64(),
            self.max_concurrent,
        );

        Ok(())
    }

    /// Drop the serve process (kills process, joins reader thread).
    /// Sends LSP shutdown/exit first if the server is still reachable.
    fn drop_serve(&mut self) {
        if self.serve.is_some() {
            // Best-effort LSP shutdown — may fail if server already crashed.
            let shutdown_id = self.next_lsp_id;
            self.next_lsp_id += 1;
            let _ = self.lsp_send_raw(&serde_json::to_vec(&serde_json::json!({
                "jsonrpc": "2.0",
                "id": shutdown_id,
                "method": "shutdown",
                "params": {},
            })).unwrap());
            let _ = self.lsp_notify("exit", serde_json::json!({}));
        }
        // Drop triggers SIGKILL + join.
        self.serve = None;
    }

    /// Drain stale `LspCrashed`/`LspMessage` from the channel after dropping
    /// a ServeProcess. The drop joins the reader thread, so all its messages
    /// are in the channel by the time this runs. Returns true if a Shutdown
    /// was received (caller should stop).
    fn drain_stale_lsp_messages(&mut self) -> bool {
        loop {
            match self.cmd_rx.try_recv() {
                Ok(Cmd::LspCrashed | Cmd::LspMessage(_)) => continue,
                Ok(Cmd::Check { respond, .. } | Cmd::Restart { respond }) => {
                    let _ = respond.send(Err(LeanError::ServerRestarted));
                }
                Ok(Cmd::FileChanged(p)) => { self.pending_changes.insert(p); }
                Ok(Cmd::LayoutChanged) => { self.layout_changed = true; }
                Ok(Cmd::Shutdown { respond }) => {
                    self.shutting_down = true;
                    let _ = respond.send(());
                    return true;
                }
                Err(_) => return false,
            }
        }
    }

    fn restart_if_stale(&mut self) {
        if !self.layout_changed {
            return;
        }
        eprintln!("[lean] File layout changed, restarting lake serve...");
        self.drop_serve();
        if self.drain_stale_lsp_messages() { return; }
        if let Err(e) = self.start_lake_serve() {
            eprintln!("[lean] Failed to restart: {e}");
        }
    }

    fn handle_lsp_crash(&mut self) {
        eprintln!("[lean] lake serve crashed, restarting...");
        self.fail_all_pending();
        self.drop_serve();
        if self.drain_stale_lsp_messages() { return; }
        if let Err(e) = self.start_lake_serve() {
            eprintln!("[lean] Failed to restart after crash: {e}");
        }
    }

    // -- LSP I/O ------------------------------------------------------------

    fn lsp_send_raw(&mut self, body: &[u8]) -> Result<()> {
        let stdin = &mut self.serve.as_mut().ok_or(LeanError::LspNotStarted)?.stdin;
        let header = format!("Content-Length: {}\r\n\r\n", body.len());
        stdin.write_all(header.as_bytes())?;
        stdin.write_all(body)?;
        stdin.flush()?;
        Ok(())
    }

    fn lsp_notify(&mut self, method: &str, params: Value) -> Result<()> {
        let body = serde_json::to_vec(&serde_json::json!({
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
        }))?;
        self.lsp_send_raw(&body)
    }

    // -- LSP message dispatch -----------------------------------------------

    fn handle_lsp_message(&mut self, msg: Value) {
        let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");

        match method {
            "textDocument/publishDiagnostics" => {
                if let Some(params) = msg.get("params") {
                    if let Some(uri) = params.get("uri").and_then(|v| v.as_str()) {
                        let uri = uri.to_string();
                        let diags = params
                            .get("diagnostics")
                            .cloned()
                            .and_then(|v| v.as_array().cloned())
                            .unwrap_or_default();
                        if let Some(fs) = self.files.get_mut(&uri) {
                            fs.diagnostics = diags;
                            fs.diagnostics_received = true;
                        }
                        self.try_signal_completion(&uri);
                    }
                }
            }
            "$/lean/fileProgress" => {
                if let Some(params) = msg.get("params") {
                    if let Some(uri) = params
                        .get("textDocument")
                        .and_then(|td| td.get("uri"))
                        .and_then(|v| v.as_str())
                    {
                        let processing_empty = params
                            .get("processing")
                            .and_then(|v| v.as_array())
                            .map(|a| a.is_empty())
                            .unwrap_or(false);
                        if processing_empty {
                            let uri = uri.to_string();
                            if let Some(fs) = self.files.get_mut(&uri) {
                                fs.progress_done = true;
                            }
                            self.try_signal_completion(&uri);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn try_signal_completion(&mut self, uri: &str) {
        let fs = match self.files.get(uri) {
            Some(fs) if fs.progress_done && fs.diagnostics_received => fs,
            _ => return,
        };

        if fs.pending_checks.is_empty() {
            return;
        }

        let diagnostics = fs.diagnostics.clone();
        let checks = std::mem::take(&mut self.files.get_mut(uri).unwrap().pending_checks);

        let mut to_close = Vec::new();
        for check in checks {
            let dt = check.t0.elapsed().as_secs_f64();
            let _ = check.respond.send(Ok(serde_json::json!({
                "file": check.filepath,
                "time_seconds": (dt * 100.0).round() / 100.0,
                "diagnostics": diagnostics,
            })));
            if check.close_after {
                to_close.push(check.filepath);
            }
        }
        for filepath in to_close {
            self.close_uri(&self.file_uri(&filepath));
        }

        self.active_count = self.active_count.saturating_sub(1);
        self.drain_queue();
    }

    fn drain_queue(&mut self) {
        while self.active_count < self.max_concurrent {
            if let Some(queued) = self.check_queue.pop_front() {
                self.active_count += 1;
                self.start_check(&queued.filepath, queued.close_after, queued.respond);
            } else {
                break;
            }
        }
        self.debug_assert_active_count();
    }

    // -- File operations ----------------------------------------------------

    fn file_uri(&self, filepath: &str) -> String {
        let abspath = if filepath.starts_with('/') {
            PathBuf::from(filepath)
        } else {
            self.project_root.join(filepath)
        };
        path_to_uri(&abspath)
    }

    /// Strip the `file://` prefix and project root from a URI for logging.
    fn uri_to_relpath<'a>(&self, uri: &'a str) -> &'a str {
        let root_uri = path_to_uri(&self.project_root);
        uri.strip_prefix(&root_uri)
            .and_then(|s| s.strip_prefix('/'))
            .unwrap_or(uri)
    }

    /// Close a file by URI: fail pending checks, decrement active_count,
    /// remove FileState, and send didClose to the LSP.
    fn close_uri(&mut self, uri: &str) {
        if let Some(fs) = self.files.remove(uri) {
            if !fs.pending_checks.is_empty() {
                self.active_count = self.active_count.saturating_sub(1);
                for check in fs.pending_checks {
                    let _ = check.respond.send(Err(LeanError::ServerRestarted));
                }
            }
            let _ = self.lsp_notify(
                "textDocument/didClose",
                serde_json::json!({"textDocument": {"uri": uri}}),
            );
        }
    }

    fn sync_changed_files(&mut self, target_uri: &str) -> bool {
        if self.pending_changes.is_empty() {
            return false;
        }

        let deps_changed = self.pending_changes.iter().any(|relpath| {
            let abspath = self.project_root.join(relpath);
            let uri = path_to_uri(&abspath);
            uri != target_uri
        });

        let to_notify: Vec<String> = self.pending_changes.drain().collect();
        let mut watched_changes = Vec::new();

        for relpath in &to_notify {
            let abspath = self.project_root.join(relpath);
            let uri = path_to_uri(&abspath);

            if uri == target_uri {
                continue;
            }

            self.close_uri(&uri);
            watched_changes.push(serde_json::json!({"uri": uri, "type": 2}));
        }

        if !watched_changes.is_empty() {
            let _ = self.lsp_notify(
                "workspace/didChangeWatchedFiles",
                serde_json::json!({"changes": watched_changes}),
            );
        }

        deps_changed
    }

    fn start_check(
        &mut self,
        filepath: &str,
        close_after: bool,
        respond: SyncSender<Result<Value>>,
    ) {
        let uri = self.file_uri(filepath);
        let abspath = self.project_root.join(filepath);

        let deps_changed = self.sync_changed_files(&uri);

        let content = match fs::read_to_string(&abspath) {
            Ok(c) => c,
            Err(e) => return self.fail_check(respond, LeanError::Io(e)),
        };

        if deps_changed && self.files.contains_key(&uri) {
            eprintln!("[lean] Dependencies changed, reopening {filepath}");
            self.close_uri(&uri);
        }

        let t0 = Instant::now();

        let send_result = if let Some(fs) = self.files.get_mut(&uri) {
            let version = fs.bump_version();
            fs.reset_check();
            self.lsp_notify(
                "textDocument/didChange",
                serde_json::json!({
                    "textDocument": {"uri": uri, "version": version},
                    "contentChanges": [{"text": content}],
                }),
            )
        } else {
            self.files.insert(uri.clone(), FileState::new_opened());
            self.lsp_notify(
                "textDocument/didOpen",
                serde_json::json!({
                    "textDocument": {
                        "uri": uri,
                        "languageId": "lean4",
                        "version": 1,
                        "text": content,
                    },
                }),
            )
        };

        if let Err(e) = send_result {
            return self.fail_check(respond, e);
        }

        self.files.get_mut(&uri).unwrap().pending_checks.push(PendingCheck {
            filepath: filepath.to_string(),
            t0,
            close_after,
            respond,
        });
    }

    /// Fail a check that couldn't be started; gives back the active slot.
    fn fail_check(&mut self, respond: SyncSender<Result<Value>>, e: LeanError) {
        let _ = respond.send(Err(e));
        self.active_count = self.active_count.saturating_sub(1);
        self.drain_queue();
    }

    /// Close files that haven't been checked in >10 minutes.
    fn evict_idle_files(&mut self) {
        let cutoff = Duration::from_secs(600);
        let now = Instant::now();
        let stale: Vec<String> = self.files.iter()
            .filter(|(_, fs)| {
                now.duration_since(fs.last_active) > cutoff
                    && fs.pending_checks.is_empty()
            })
            .map(|(uri, _)| uri.clone())
            .collect();

        for uri in &stale {
            let relpath = self.uri_to_relpath(uri).to_string();
            self.close_uri(uri);
            eprintln!("[lean] Evicted idle file: {relpath}");
        }
    }
}

fn read_lsp_message(reader: &mut BufReader<ChildStdout>) -> Option<Value> {
    let mut header_line = String::new();
    let mut content_length: usize = 0;

    loop {
        header_line.clear();
        match reader.read_line(&mut header_line) {
            Ok(0) | Err(_) => return None,
            Ok(_) => {}
        }
        let trimmed = header_line.trim();
        if trimmed.is_empty() {
            break;
        }
        if let Some(val) = trimmed.strip_prefix("Content-Length: ") {
            if let Ok(len) = val.parse::<usize>() {
                content_length = len;
            }
        }
    }

    if content_length == 0 {
        return None;
    }

    let mut body = vec![0u8; content_length];
    reader.read_exact(&mut body).ok()?;
    serde_json::from_slice(&body).ok()
}

fn lsp_reader_thread(cmd_tx: Sender<Cmd>, stdout: ChildStdout) {
    let mut reader = BufReader::new(stdout);
    loop {
        match read_lsp_message(&mut reader) {
            Some(msg) => {
                if cmd_tx.send(Cmd::LspMessage(msg)).is_err() {
                    break;
                }
            }
            None => {
                let _ = cmd_tx.send(Cmd::LspCrashed);
                break;
            }
        }
    }
}

fn start_watcher(project_root: &Path, cmd_tx: Sender<Cmd>) -> Option<RecommendedWatcher> {
    let root = project_root.to_path_buf();

    let mut watcher =
        notify::recommended_watcher(move |res: std::result::Result<Event, notify::Error>| {
            if let Ok(event) = res {
                for path in &event.paths {
                    if path.extension().and_then(|e| e.to_str()) != Some("lean") {
                        continue;
                    }
                    if let Ok(rel) = path.strip_prefix(&root) {
                        let relpath = rel.to_string_lossy().to_string();
                        if relpath.starts_with(".lake") {
                            continue;
                        }
                        match event.kind {
                            EventKind::Create(_) | EventKind::Remove(_) => {
                                let _ = cmd_tx.send(Cmd::LayoutChanged);
                                let _ = cmd_tx.send(Cmd::FileChanged(relpath));
                            }
                            EventKind::Modify(_) => {
                                let _ = cmd_tx.send(Cmd::FileChanged(relpath));
                            }
                            _ => {}
                        }
                    }
                }
            }
        })
        .ok()?;

    let _ = watcher.watch(project_root, RecursiveMode::NonRecursive);
    for dir in &["AKS", "Bench", "rust", "Random"] {
        let d = project_root.join(dir);
        if d.is_dir() {
            let _ = watcher.watch(&d, RecursiveMode::Recursive);
        }
    }

    Some(watcher)
}

fn run_snippet(project_root: &Path, code: &str) -> String {
    match Command::new("lake")
        .args(["env", "lean", "--stdin"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .current_dir(project_root)
        .spawn()
    {
        Ok(mut child) => {
            if let Some(mut stdin) = child.stdin.take() {
                let _ = stdin.write_all(code.as_bytes());
            }
            match child.wait_with_output() {
                Ok(output) => {
                    let mut parts = Vec::new();
                    if !output.stdout.is_empty() {
                        parts.push(String::from_utf8_lossy(&output.stdout).into_owned());
                    }
                    if !output.stderr.is_empty() {
                        parts.push(String::from_utf8_lossy(&output.stderr).into_owned());
                    }
                    if parts.is_empty() { "(no output)".to_string() } else { parts.join("\n") }
                }
                Err(e) => format!("ERROR: {e}"),
            }
        }
        Err(e) => format!("ERROR: {e}"),
    }
}

fn format_check_result(result: &Value) -> String {
    let file = result.get("file").and_then(|v| v.as_str()).unwrap_or("?");
    let time = result.get("time_seconds").and_then(|v| v.as_f64()).unwrap_or(0.0);
    let diagnostics = result.get("diagnostics").and_then(|v| v.as_array());

    let mut out = format!("Checked {file} in {time:.2}s");
    let Some(diags) = diagnostics.filter(|a| !a.is_empty()) else {
        out.push_str("\nNo errors or warnings.");
        return out;
    };
    for d in diags {
        let severity = d.get("severity").and_then(|v| v.as_u64()).unwrap_or(0);
        let label = match severity { 1 => "error", 2 => "warning", _ => "info" };
        let rng = d.get("range").and_then(|r| r.get("start"));
        let line = rng.and_then(|s| s.get("line")).and_then(|v| v.as_u64()).unwrap_or(0) + 1;
        let col = rng.and_then(|s| s.get("character")).and_then(|v| v.as_u64()).unwrap_or(0);
        let msg = d.get("message").and_then(|v| v.as_str()).unwrap_or("");
        out.push_str(&format!("\n  {label} [{line}:{col}]: {msg}"));
    }
    out
}

fn path_to_uri(path: &Path) -> String {
    format!("file://{}", path.to_string_lossy())
}

fn mcp_write(msg: Value) {
    let line = serde_json::to_string(&msg).unwrap();
    let stdout = io::stdout();
    let mut out = stdout.lock();
    let _ = out.write_all(line.as_bytes());
    let _ = out.write_all(b"\n");
    let _ = out.flush();
}

fn mcp_reply(id: &Value, result: Value) {
    mcp_write(serde_json::json!({"jsonrpc": "2.0", "id": id, "result": result}));
}

fn mcp_error(id: &Value, code: i64, message: &str) {
    mcp_write(serde_json::json!({"jsonrpc": "2.0", "id": id, "error": {"code": code, "message": message}}));
}

fn main() {
    let project_root = env::var("PROJECT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            let self_path = PathBuf::from(file!());
            if let Some(root) = self_path.parent().and_then(|p| p.parent()).and_then(|p| p.parent()) {
                root.to_path_buf()
            } else {
                env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
            }
        });

    let (cmd_tx, cmd_rx) = mpsc::channel();
    let (ready_tx, ready_rx) = mpsc::sync_channel(1);

    let coord_root = project_root.clone();
    let coord = Coordinator::new(coord_root, cmd_rx, cmd_tx.clone(), ready_tx);
    thread::Builder::new()
        .name("coordinator".into())
        .spawn(move || coord.run())
        .expect("Failed to spawn coordinator");

    if ready_rx.recv_timeout(Duration::from_secs(120)).is_err() {
        eprintln!("[lean] Coordinator failed to start within 120s");
        process::exit(1);
    }

    eprintln!("[lean] MCP server ready");

    // Signal handler: SIGTERM/SIGINT trigger coordinator shutdown
    {
        let tx = cmd_tx.clone();
        thread::Builder::new()
            .name("signal-handler".into())
            .spawn(move || {
                use nix::sys::signal::{SigSet, Signal};
                let mut mask = SigSet::empty();
                mask.add(Signal::SIGTERM);
                mask.add(Signal::SIGINT);
                let _ = mask.thread_block();
                if let Ok(_sig) = mask.wait() {
                    eprintln!("[lean] Received signal, shutting down...");
                    let (resp_tx, _) = mpsc::sync_channel(1);
                    let _ = tx.send(Cmd::Shutdown { respond: resp_tx });
                    thread::sleep(Duration::from_millis(500));
                    process::exit(0);
                }
            })
            .expect("Failed to spawn signal handler");
        let mut mask = nix::sys::signal::SigSet::empty();
        mask.add(nix::sys::signal::Signal::SIGTERM);
        mask.add(nix::sys::signal::Signal::SIGINT);
        let _ = mask.thread_block();
    }

    // MCP message loop on stdin
    let stdin = io::stdin();
    let reader = stdin.lock();
    for line in reader.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        if line.is_empty() {
            continue;
        }

        let msg: Value = match serde_json::from_str(&line) {
            Ok(v) => v,
            Err(_) => continue,
        };

        let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");
        let req_id = msg.get("id").cloned().unwrap_or(Value::Null);

        match method {
            "initialize" => {
                let client_version = msg.get("params")
                    .and_then(|p| p.get("protocolVersion"))
                    .and_then(|v| v.as_str())
                    .unwrap_or("2025-11-25");
                mcp_reply(&req_id, serde_json::json!({
                    "protocolVersion": client_version,
                    "capabilities": {"tools": {}},
                    "serverInfo": {"name": "lean", "version": "0.2.0"},
                }));
            }

            "notifications/initialized" => {}

            "tools/list" => {
                mcp_reply(&req_id, serde_json::json!({
                    "tools": [
                        {
                            "name": "snippet",
                            "description": "Run an ad-hoc Lean 4 snippet (imports, #check, #eval, proofs, etc.) via `lake env lean --stdin`. Returns compiler output.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "code": {
                                        "type": "string",
                                        "description": "Lean 4 code to evaluate",
                                    }
                                },
                                "required": ["code"],
                            },
                        },
                        {
                            "name": "restart",
                            "description": "Restart the lake serve LSP server, clearing all state. Use when imports are out of date after rebuilding dependencies.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {},
                            },
                        },
                        {
                            "name": "check",
                            "description": "Check a Lean file using the persistent lake serve LSP. Fast incremental checking (~0.2-2s for warm edits). Returns errors and warnings.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "file": {
                                        "type": "string",
                                        "description": "Relative path to the .lean file (e.g. 'AKS/Separator/Family.lean')",
                                    },
                                    "close_after": {
                                        "type": "boolean",
                                        "description": "Close the file after checking (frees LSP memory). Default false.",
                                    },
                                },
                                "required": ["file"],
                            },
                        },
                    ]
                }));
            }

            "tools/call" => {
                let params = msg.get("params").cloned().unwrap_or(Value::Null);
                let name = params.get("name").and_then(|v| v.as_str()).unwrap_or("");
                let args = params.get("arguments").cloned().unwrap_or(Value::Null);

                match name {
                    "snippet" => {
                        let code = args.get("code").and_then(|v| v.as_str()).unwrap_or("");
                        let text = run_snippet(&project_root, code);
                        mcp_reply(&req_id, serde_json::json!({
                            "content": [{"type": "text", "text": text}]
                        }));
                    }
                    "restart" => {
                        let (tx, rx) = mpsc::sync_channel(1);
                        if cmd_tx.send(Cmd::Restart { respond: tx }).is_err() {
                            mcp_error(&req_id, -32603, "Coordinator dead");
                            continue;
                        }
                        match rx.recv_timeout(Duration::from_secs(120)) {
                            Ok(Ok(_)) => {
                                mcp_reply(&req_id, serde_json::json!({
                                    "content": [{"type": "text", "text": "Restarted lake serve successfully."}]
                                }));
                            }
                            Ok(Err(e)) => {
                                mcp_reply(&req_id, serde_json::json!({
                                    "content": [{"type": "text", "text": format!("ERROR: restart failed: {e}")}],
                                    "isError": true,
                                }));
                            }
                            Err(_) => {
                                mcp_reply(&req_id, serde_json::json!({
                                    "content": [{"type": "text", "text": "ERROR: restart timed out (120s)"}],
                                    "isError": true,
                                }));
                            }
                        }
                    }
                    "check" => {
                        let file = match args.get("file").and_then(|v| v.as_str()) {
                            Some(f) => f.to_string(),
                            None => {
                                mcp_error(&req_id, -32602, "Missing 'file' argument");
                                continue;
                            }
                        };
                        let close_after = args.get("close_after")
                            .and_then(|v| v.as_bool())
                            .unwrap_or(false);

                        let (tx, rx) = mpsc::sync_channel(1);
                        if cmd_tx.send(Cmd::Check {
                            file: file.clone(),
                            close_after,
                            respond: tx,
                        }).is_err() {
                            mcp_error(&req_id, -32603, "Coordinator dead");
                            continue;
                        }

                        match rx.recv_timeout(Duration::from_secs(600)) {
                            Ok(Ok(result)) => {
                                let text = format_check_result(&result);
                                mcp_reply(&req_id, serde_json::json!({
                                    "content": [{"type": "text", "text": text}]
                                }));
                            }
                            Ok(Err(e)) => {
                                mcp_reply(&req_id, serde_json::json!({
                                    "content": [{"type": "text", "text": format!("ERROR: {e}")}],
                                    "isError": true,
                                }));
                            }
                            Err(_) => {
                                mcp_reply(&req_id, serde_json::json!({
                                    "content": [{"type": "text", "text": "ERROR: check timed out (600s)"}],
                                    "isError": true,
                                }));
                            }
                        }
                    }
                    _ => {
                        mcp_error(&req_id, -32601, &format!("Unknown tool: {name}"));
                    }
                }
            }

            "ping" => {
                mcp_reply(&req_id, serde_json::json!({}));
            }

            _ => {
                if req_id != Value::Null {
                    mcp_error(&req_id, -32601, &format!("Unknown method: {method}"));
                }
            }
        }
    }

    // stdin closed — shut down
    let (tx, rx) = mpsc::sync_channel(1);
    let _ = cmd_tx.send(Cmd::Shutdown { respond: tx });
    let _ = rx.recv_timeout(Duration::from_secs(5));
}
