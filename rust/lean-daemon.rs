#!/usr/bin/env -S cargo +nightly -Zscript
---cargo
[dependencies]
notify = "8"
serde = { version = "1", features = ["derive"] }
serde_json = "1"
md-5 = "0.10"
glob = "0.3"

[profile.release]
opt-level = 2
---

//! Persistent Lean language server daemon for fast incremental checking.
//!
//! Rust port of scripts/lean-daemon.py with inotify-based file watching
//! (via the `notify` crate) instead of mtime polling.
//!
//! Architecture:
//!   - Starts `lake serve` as a subprocess and communicates via LSP (JSON-RPC)
//!   - Listens on a Unix domain socket for check requests
//!   - Uses inotify (via notify crate) to detect file changes instantly
//!   - When a file is checked, sends textDocument/didOpen or didChange to the server
//!   - Waits for full file processing (via $/lean/fileProgress) before returning
//!   - Collects all diagnostics and returns them to the client

use glob::glob;
use md5::{Digest, Md5};
use notify::{Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use serde_json::Value;
use std::collections::{HashMap, HashSet};
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, SyncSender};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use std::{env, fs, process, thread};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

struct LspState {
    /// stdin of the lake serve process (None before start)
    lsp_stdin: Option<ChildStdin>,
    next_id: u64,
    /// Pending LSP request ID -> oneshot sender for response
    pending: HashMap<u64, SyncSender<Value>>,
    /// URI -> latest diagnostics array
    diagnostics: HashMap<String, Vec<Value>>,
    /// URI -> whether fileProgress:[] (empty processing) was received
    progress_done: HashMap<String, bool>,
    /// URI -> whether publishDiagnostics was received
    diagnostics_received: HashMap<String, bool>,
    /// URI -> list of senders to notify when file is done
    file_done_senders: HashMap<String, Vec<SyncSender<()>>>,
    /// URI -> version counter for opened files
    opened_files: HashMap<String, u64>,
    /// Relative paths of files changed since last sync (from notify events)
    changed_files: HashSet<String>,
    /// Snapshot of project .lean files for layout change detection
    file_snapshot: HashSet<String>,
}

impl LspState {
    fn new() -> Self {
        LspState {
            lsp_stdin: None,
            next_id: 1,
            pending: HashMap::new(),
            diagnostics: HashMap::new(),
            progress_done: HashMap::new(),
            diagnostics_received: HashMap::new(),
            file_done_senders: HashMap::new(),
            opened_files: HashMap::new(),
            changed_files: HashSet::new(),
            file_snapshot: HashSet::new(),
        }
    }

    /// Reset all LSP-related state (for restart). Keeps changed_files.
    fn reset(&mut self) {
        self.lsp_stdin = None;
        self.next_id = 1;
        self.pending.clear();
        self.diagnostics.clear();
        self.progress_done.clear();
        self.diagnostics_received.clear();
        // Signal any waiters that we're shutting down
        for (_, senders) in self.file_done_senders.drain() {
            drop(senders); // receivers will get RecvError
        }
        self.opened_files.clear();
    }

    fn send_raw(&mut self, body: &[u8]) -> std::io::Result<()> {
        let stdin = self
            .lsp_stdin
            .as_mut()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::NotConnected, "LSP not started"))?;
        let header = format!("Content-Length: {}\r\n\r\n", body.len());
        stdin.write_all(header.as_bytes())?;
        stdin.write_all(body)?;
        stdin.flush()
    }
}

/// Daemon handle. All mutable state is behind Arc<Mutex<>>, so this is
/// cheaply cloneable and can be shared across threads without a top-level lock.
#[derive(Clone)]
struct Daemon {
    state: Arc<Mutex<LspState>>,
    lake_proc: Arc<Mutex<Option<Child>>>,
    watcher: Arc<Mutex<Option<RecommendedWatcher>>>,
    project_root: PathBuf,
    layout_changed: Arc<AtomicBool>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn project_hash(root: &Path) -> String {
    let mut hasher = Md5::new();
    hasher.update(root.to_string_lossy().as_bytes());
    let result = hasher.finalize();
    format!(
        "{:02x}{:02x}{:02x}{:02x}",
        result[0], result[1], result[2], result[3]
    )
}

fn socket_path(hash: &str) -> String {
    format!("/tmp/lean-daemon-{}.sock", hash)
}

fn snapshot_lean_files(root: &Path) -> HashSet<String> {
    let mut files = HashSet::new();
    for pattern in &["*.lean", "AKS/**/*.lean"] {
        let full_pattern = root.join(pattern).to_string_lossy().to_string();
        if let Ok(paths) = glob(&full_pattern) {
            for entry in paths.flatten() {
                if let Ok(rel) = entry.strip_prefix(root) {
                    files.insert(rel.to_string_lossy().to_string());
                }
            }
        }
    }
    files
}

fn path_to_uri(path: &Path) -> String {
    format!("file://{}", path.to_string_lossy())
}

// ---------------------------------------------------------------------------
// LSP I/O (free functions that take the Arc<Mutex<LspState>>)
// ---------------------------------------------------------------------------

fn send_lsp_message(state: &Arc<Mutex<LspState>>, msg: &Value) -> std::io::Result<()> {
    let body = serde_json::to_vec(msg)?;
    state.lock().unwrap().send_raw(&body)
}

fn send_request(
    state: &Arc<Mutex<LspState>>,
    method: &str,
    params: Value,
) -> Result<Value, String> {
    let (tx, rx) = mpsc::sync_channel(1);
    let id = {
        let mut st = state.lock().unwrap();
        let id = st.next_id;
        st.next_id += 1;
        st.pending.insert(id, tx);
        id
    };

    let msg = serde_json::json!({
        "jsonrpc": "2.0",
        "id": id,
        "method": method,
        "params": params,
    });
    send_lsp_message(state, &msg).map_err(|e| format!("send error: {e}"))?;

    rx.recv_timeout(Duration::from_secs(60))
        .map_err(|e| format!("LSP request {method} timed out: {e}"))
}

fn send_notify(
    state: &Arc<Mutex<LspState>>,
    method: &str,
    params: Value,
) -> std::io::Result<()> {
    let msg = serde_json::json!({
        "jsonrpc": "2.0",
        "method": method,
        "params": params,
    });
    send_lsp_message(state, &msg)
}

/// Read one LSP Content-Length framed message from the reader.
fn read_lsp_message(reader: &mut BufReader<ChildStdout>) -> Option<Value> {
    let mut header_line = String::new();
    let mut content_length: usize = 0;

    // Read headers until blank line
    loop {
        header_line.clear();
        match reader.read_line(&mut header_line) {
            Ok(0) => return None, // EOF
            Err(_) => return None,
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
    if reader.read_exact(&mut body).is_err() {
        return None;
    }

    serde_json::from_slice(&body).ok()
}

/// LSP reader thread: reads messages from lake serve stdout and dispatches.
fn lsp_reader_thread(state: Arc<Mutex<LspState>>, stdout: ChildStdout) {
    let mut reader = BufReader::new(stdout);

    loop {
        let msg = match read_lsp_message(&mut reader) {
            Some(m) => m,
            None => {
                eprintln!("[lean-daemon] LSP reader: EOF or error, exiting reader thread");
                break;
            }
        };

        // Handle responses to our requests
        if let Some(id) = msg.get("id").and_then(|v| v.as_u64()) {
            let sender = state.lock().unwrap().pending.remove(&id);
            if let Some(tx) = sender {
                let _ = tx.send(msg);
                continue;
            }
        }

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

                        let mut st = state.lock().unwrap();
                        st.diagnostics.insert(uri.clone(), diags);
                        st.diagnostics_received.insert(uri.clone(), true);

                        // If progress also done, signal completion
                        if st.progress_done.get(&uri).copied().unwrap_or(false) {
                            if let Some(senders) = st.file_done_senders.remove(&uri) {
                                for tx in senders {
                                    let _ = tx.send(());
                                }
                            }
                        }
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
                            let mut st = state.lock().unwrap();
                            st.progress_done.insert(uri.clone(), true);

                            // If diagnostics also received, signal completion
                            if st.diagnostics_received.get(&uri).copied().unwrap_or(false) {
                                if let Some(senders) = st.file_done_senders.remove(&uri) {
                                    for tx in senders {
                                        let _ = tx.send(());
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// File watcher
// ---------------------------------------------------------------------------

fn start_watcher(
    project_root: &Path,
    state: Arc<Mutex<LspState>>,
    layout_changed: Arc<AtomicBool>,
) -> Option<RecommendedWatcher> {
    let root = project_root.to_path_buf();

    let mut watcher =
        notify::recommended_watcher(move |res: Result<Event, notify::Error>| match res {
            Ok(event) => {
                for path in &event.paths {
                    // Only care about .lean files
                    if path.extension().and_then(|e| e.to_str()) != Some("lean") {
                        continue;
                    }
                    // Skip .lake directory
                    if let Ok(rel) = path.strip_prefix(&root) {
                        let relpath = rel.to_string_lossy().to_string();
                        if relpath.starts_with(".lake") {
                            continue;
                        }

                        match event.kind {
                            EventKind::Create(_) | EventKind::Remove(_) => {
                                layout_changed.store(true, Ordering::SeqCst);
                                state.lock().unwrap().changed_files.insert(relpath);
                            }
                            EventKind::Modify(_) => {
                                state.lock().unwrap().changed_files.insert(relpath);
                            }
                            _ => {}
                        }
                    }
                }
            }
            Err(e) => {
                eprintln!("[lean-daemon] File watcher error: {e}");
            }
        })
        .ok()?;

    // Watch project root non-recursively (top-level .lean files)
    let _ = watcher.watch(project_root, RecursiveMode::NonRecursive);

    // Watch AKS/ recursively
    let aks_dir = project_root.join("AKS");
    if aks_dir.is_dir() {
        let _ = watcher.watch(&aks_dir, RecursiveMode::Recursive);
    }

    // Watch Bench/ recursively
    let bench_dir = project_root.join("Bench");
    if bench_dir.is_dir() {
        let _ = watcher.watch(&bench_dir, RecursiveMode::Recursive);
    }

    Some(watcher)
}

// ---------------------------------------------------------------------------
// Daemon core
// ---------------------------------------------------------------------------

impl Daemon {
    fn new(project_root: PathBuf) -> Self {
        Daemon {
            state: Arc::new(Mutex::new(LspState::new())),
            lake_proc: Arc::new(Mutex::new(None)),
            watcher: Arc::new(Mutex::new(None)),
            project_root,
            layout_changed: Arc::new(AtomicBool::new(false)),
        }
    }

    fn start(&self) -> Result<(), String> {
        // Build CertCheck shared lib first
        eprintln!("[lean-daemon] Building CertCheck shared lib...");
        let _ = Command::new("lake")
            .args(["build", "CertCheck:shared"])
            .current_dir(&self.project_root)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();

        // Spawn lake serve
        let certcheck_lib = self
            .project_root
            .join(".lake/build/lib/libaks_CertCheck.so");
        let plugin_arg = format!("--plugin={}", certcheck_lib.to_string_lossy());

        eprintln!(
            "[lean-daemon] Starting lake serve in {}...",
            self.project_root.display()
        );
        let mut proc = Command::new("lake")
            .args(["serve", "--", &plugin_arg])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .current_dir(&self.project_root)
            .spawn()
            .map_err(|e| format!("Failed to spawn lake serve: {e}"))?;

        let stdin = proc.stdin.take().ok_or("No stdin")?;
        let stdout = proc.stdout.take().ok_or("No stdout")?;

        // Store stdin and reset state
        {
            let mut st = self.state.lock().unwrap();
            st.reset();
            st.lsp_stdin = Some(stdin);
            st.file_snapshot = snapshot_lean_files(&self.project_root);
        }

        *self.lake_proc.lock().unwrap() = Some(proc);

        // Start LSP reader thread
        let state_clone = Arc::clone(&self.state);
        thread::Builder::new()
            .name("lsp-reader".into())
            .spawn(move || lsp_reader_thread(state_clone, stdout))
            .map_err(|e| format!("Failed to spawn reader thread: {e}"))?;

        // Initialize LSP
        let t0 = Instant::now();
        let root_uri = path_to_uri(&self.project_root);
        send_request(
            &self.state,
            "initialize",
            serde_json::json!({
                "processId": process::id(),
                "rootUri": root_uri,
                "capabilities": {
                    "textDocument": {
                        "publishDiagnostics": {"relatedInformation": true}
                    }
                },
            }),
        )?;
        send_notify(&self.state, "initialized", serde_json::json!({}))
            .map_err(|e| format!("Failed to send initialized: {e}"))?;

        let dt = t0.elapsed().as_secs_f64();
        eprintln!("[lean-daemon] Initialized in {dt:.1}s");

        // Start file watcher
        let w = start_watcher(
            &self.project_root,
            Arc::clone(&self.state),
            Arc::clone(&self.layout_changed),
        );
        if w.is_some() {
            eprintln!("[lean-daemon] File watcher started (inotify)");
        } else {
            eprintln!("[lean-daemon] Warning: file watcher failed to start");
        }
        *self.watcher.lock().unwrap() = w;

        Ok(())
    }

    fn sync_changed_files(&self, target_uri: &str) {
        // Drain changed files from the watcher
        let changed: Vec<String> = {
            let mut st = self.state.lock().unwrap();
            st.changed_files.drain().collect()
        };

        if changed.is_empty() {
            return;
        }

        let mut watched_changes = Vec::new();

        for relpath in &changed {
            let abspath = self.project_root.join(relpath);
            let uri = path_to_uri(&abspath);

            if uri == target_uri {
                continue; // handled by check_file
            }

            let is_opened = self.state.lock().unwrap().opened_files.contains_key(&uri);

            if is_opened {
                // File is open — send didChange with new content
                if let Ok(content) = fs::read_to_string(&abspath) {
                    let version = {
                        let mut st = self.state.lock().unwrap();
                        let v = st.opened_files.get_mut(&uri).unwrap();
                        *v += 1;
                        *v
                    };
                    let _ = send_notify(
                        &self.state,
                        "textDocument/didChange",
                        serde_json::json!({
                            "textDocument": {"uri": uri, "version": version},
                            "contentChanges": [{"text": content}],
                        }),
                    );
                }
            } else {
                // File not open — tell server it changed on disk
                watched_changes.push(serde_json::json!({"uri": uri, "type": 2}));
            }
        }

        if !watched_changes.is_empty() {
            let _ = send_notify(
                &self.state,
                "workspace/didChangeWatchedFiles",
                serde_json::json!({"changes": watched_changes}),
            );
        }
    }

    fn check_file(&self, filepath: &str) -> Result<Value, String> {
        let abspath = if filepath.starts_with('/') {
            PathBuf::from(filepath)
        } else {
            self.project_root.join(filepath)
        };
        let uri = path_to_uri(&abspath);

        // Sync any dependency files that changed
        self.sync_changed_files(&uri);

        let content =
            fs::read_to_string(&abspath).map_err(|e| format!("Failed to read {filepath}: {e}"))?;

        let t0 = Instant::now();

        // Prepare wait state and send didOpen/didChange in one lock scope.
        // This prevents a race where the reader thread signals completion
        // between prepare_wait and registering the sender.
        let (tx, rx) = mpsc::sync_channel(1);
        {
            let mut st = self.state.lock().unwrap();

            // Reset completion tracking
            st.progress_done.insert(uri.clone(), false);
            st.diagnostics_received.insert(uri.clone(), false);
            st.diagnostics.remove(&uri);

            // Register completion sender
            st.file_done_senders
                .entry(uri.clone())
                .or_default()
                .push(tx);

            // Send didOpen or didChange
            if st.opened_files.contains_key(&uri) {
                let v = st.opened_files.get_mut(&uri).unwrap();
                *v += 1;
                let version = *v;
                let body = serde_json::to_vec(&serde_json::json!({
                    "jsonrpc": "2.0",
                    "method": "textDocument/didChange",
                    "params": {
                        "textDocument": {"uri": uri, "version": version},
                        "contentChanges": [{"text": content}],
                    },
                }))
                .unwrap();
                let _ = st.send_raw(&body);
            } else {
                st.opened_files.insert(uri.clone(), 1);
                let body = serde_json::to_vec(&serde_json::json!({
                    "jsonrpc": "2.0",
                    "method": "textDocument/didOpen",
                    "params": {
                        "textDocument": {
                            "uri": uri,
                            "languageId": "lean4",
                            "version": 1,
                            "text": content,
                        },
                    },
                }))
                .unwrap();
                let _ = st.send_raw(&body);
            }
        }
        // Lock released — reader thread can now process responses

        // Wait for completion with timeout
        match rx.recv_timeout(Duration::from_secs(120)) {
            Ok(()) => {}
            Err(_) => {
                return Err(format!(
                    "File processing for {filepath} timed out after 120s"
                ));
            }
        }

        let st = self.state.lock().unwrap();
        let diagnostics = st.diagnostics.get(&uri).cloned().unwrap_or_default();
        let dt = t0.elapsed().as_secs_f64();

        Ok(serde_json::json!({
            "file": filepath,
            "time_seconds": (dt * 100.0).round() / 100.0,
            "diagnostics": diagnostics,
        }))
    }

    fn close_file(&self, filepath: &str) {
        let abspath = if filepath.starts_with('/') {
            PathBuf::from(filepath)
        } else {
            self.project_root.join(filepath)
        };
        let uri = path_to_uri(&abspath);

        let mut st = self.state.lock().unwrap();
        if st.opened_files.remove(&uri).is_some() {
            let body = serde_json::to_vec(&serde_json::json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didClose",
                "params": {
                    "textDocument": {"uri": uri},
                },
            }))
            .unwrap();
            let _ = st.send_raw(&body);
        }
    }

    fn restart_if_stale(&self) -> bool {
        // Check layout_changed flag from the file watcher
        if self.layout_changed.load(Ordering::SeqCst) {
            eprintln!("[lean-daemon] File layout changed (inotify), restarting lake serve...");
            self.layout_changed.store(false, Ordering::SeqCst);
            self.shutdown();
            if let Err(e) = self.start() {
                eprintln!("[lean-daemon] Failed to restart: {e}");
            }
            return true;
        }

        // Fallback: check file snapshot
        let current = snapshot_lean_files(&self.project_root);
        let changed = {
            let st = self.state.lock().unwrap();
            current != st.file_snapshot
        };
        if changed {
            eprintln!("[lean-daemon] File layout changed (snapshot), restarting lake serve...");
            self.shutdown();
            if let Err(e) = self.start() {
                eprintln!("[lean-daemon] Failed to restart: {e}");
            }
            return true;
        }

        false
    }

    fn shutdown(&self) {
        // Try graceful LSP shutdown (ignore errors — server may already be dead)
        let _ = send_request(&self.state, "shutdown", serde_json::json!({}));
        let _ = send_notify(&self.state, "exit", serde_json::json!({}));

        // Close stdin to unblock reader thread
        self.state.lock().unwrap().reset();

        // Kill the lake serve process
        if let Some(mut proc) = self.lake_proc.lock().unwrap().take() {
            let _ = proc.kill();
            let _ = proc.wait();
        }

        // Drop watcher
        *self.watcher.lock().unwrap() = None;
    }
}

// ---------------------------------------------------------------------------
// Socket server
// ---------------------------------------------------------------------------

fn handle_client(daemon: &Daemon, restart_lock: &Mutex<()>, mut stream: UnixStream) {
    let result: Result<String, String> = (|| {
        let mut data = Vec::new();
        let mut buf = [0u8; 4096];
        loop {
            match stream.read(&mut buf) {
                Ok(0) => break,
                Ok(n) => {
                    data.extend_from_slice(&buf[..n]);
                    if data.contains(&b'\n') {
                        break;
                    }
                }
                Err(_) => break,
            }
        }

        let request: Value =
            serde_json::from_slice(&data).map_err(|e| format!("Invalid JSON: {e}"))?;

        let command = request
            .get("command")
            .and_then(|v| v.as_str())
            .unwrap_or("");

        match command {
            "check" => {
                let file = request
                    .get("file")
                    .and_then(|v| v.as_str())
                    .ok_or("Missing 'file' field")?;
                let close_after = request
                    .get("close_after")
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false);

                // Check for layout changes under restart lock
                {
                    let _lock = restart_lock.lock().unwrap();
                    daemon.restart_if_stale();
                }

                let result = daemon.check_file(file)?;

                if close_after {
                    daemon.close_file(file);
                }

                Ok(serde_json::to_string(&result).unwrap())
            }
            "close" => {
                let file = request
                    .get("file")
                    .and_then(|v| v.as_str())
                    .ok_or("Missing 'file' field")?;
                daemon.close_file(file);
                Ok(r#"{"status":"closed"}"#.to_string())
            }
            "ping" => Ok(r#"{"status":"ok"}"#.to_string()),
            "shutdown" => {
                let response = r#"{"status":"shutting_down"}"#;
                let _ = stream.write_all(response.as_bytes());
                let _ = stream.flush();
                daemon.shutdown();
                process::exit(0);
            }
            _ => Ok(format!(r#"{{"error":"Unknown command: {}"}}"#, command)),
        }
    })();

    match result {
        Ok(response) => {
            let _ = stream.write_all(response.as_bytes());
        }
        Err(e) => {
            let err_response = serde_json::json!({"error": e});
            let _ = stream.write_all(serde_json::to_string(&err_response).unwrap().as_bytes());
        }
    }
    let _ = stream.flush();
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let project_root = env::var("PROJECT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            // When run via cargo script, cwd is the project root (set by lean-check)
            env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
        });

    let hash = project_hash(&project_root);
    let sock_path = socket_path(&hash);

    // Clean up stale socket
    let _ = fs::remove_file(&sock_path);

    let daemon = Daemon::new(project_root);
    if let Err(e) = daemon.start() {
        eprintln!("[lean-daemon] Failed to start: {e}");
        process::exit(1);
    }

    // Bind socket
    let listener = match UnixListener::bind(&sock_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("[lean-daemon] Failed to bind socket {sock_path}: {e}");
            daemon.shutdown();
            process::exit(1);
        }
    };
    eprintln!("[lean-daemon] Listening on {sock_path}");

    let restart_lock = Arc::new(Mutex::new(()));

    // Accept connections
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                let daemon = daemon.clone();
                let restart_lock = Arc::clone(&restart_lock);
                thread::Builder::new()
                    .name("client-handler".into())
                    .spawn(move || {
                        handle_client(&daemon, &restart_lock, stream);
                    })
                    .ok();
            }
            Err(e) => {
                eprintln!("[lean-daemon] Accept error: {e}");
            }
        }
    }

    // Cleanup
    daemon.shutdown();
    let _ = fs::remove_file(&sock_path);
}
