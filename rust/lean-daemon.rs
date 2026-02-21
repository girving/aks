#!/usr/bin/env -S cargo +nightly -Zscript
---cargo
[dependencies]
notify = "8"
serde_json = "1"
md-5 = "0.10"
libc = "0.2"

[profile.release]
opt-level = 2
---

//! Persistent Lean language server daemon for fast incremental checking.
//!
//! Rust port of scripts/lean-daemon.py with inotify-based file watching
//! (via the `notify` crate) instead of mtime polling.
//!
//! Architecture:
//!   A single coordinator thread owns all mutable state — no locks anywhere.
//!   Client handlers, the LSP reader, and the file watcher send commands to
//!   the coordinator via an mpsc channel. The coordinator processes them
//!   sequentially and sends results back through per-request response channels.
//!
//!   ```text
//!   Client threads  ──→ ┌─────────────┐ ──→ lake serve stdin
//!   LSP reader      ──→ │ Coordinator  │
//!   File watcher    ──→ │ (owns state) │ ──→ client response channels
//!                       └─────────────┘
//!   ```

use md5::{Digest, Md5};
use notify::{Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use serde_json::Value;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::os::unix::process::CommandExt;
use std::process::{ChildStdin, ChildStdout, Command, Stdio};
use std::os::unix::io::AsRawFd;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::mpsc::{self, Receiver, Sender, SyncSender};
use std::time::{Duration, Instant};
use std::{env, fs, process, thread};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

#[derive(Debug)]
enum DaemonError {
    Io(io::Error),
    Json(serde_json::Error),
    Timeout { operation: &'static str, seconds: u64 },
    LspNotStarted,
    ServerRestarted,
    ServerInitializing,
    MissingField(&'static str),
    CoordinatorDead,
    Other(String),
}

impl fmt::Display for DaemonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DaemonError::Io(e) => write!(f, "I/O error: {e}"),
            DaemonError::Json(e) => write!(f, "JSON error: {e}"),
            DaemonError::Timeout { operation, seconds } =>
                write!(f, "{operation} timed out after {seconds}s"),
            DaemonError::LspNotStarted => write!(f, "LSP not started"),
            DaemonError::ServerRestarted => write!(f, "Server restarted"),
            DaemonError::ServerInitializing => write!(f, "Server initializing"),
            DaemonError::MissingField(name) => write!(f, "Missing '{name}' field"),
            DaemonError::CoordinatorDead => write!(f, "Coordinator dead"),
            DaemonError::Other(msg) => write!(f, "{msg}"),
        }
    }
}

impl From<io::Error> for DaemonError {
    fn from(e: io::Error) -> Self { DaemonError::Io(e) }
}

impl From<serde_json::Error> for DaemonError {
    fn from(e: serde_json::Error) -> Self { DaemonError::Json(e) }
}

type Result<T> = std::result::Result<T, DaemonError>;

// ---------------------------------------------------------------------------
// Commands sent to the coordinator
// ---------------------------------------------------------------------------

enum Cmd {
    Check {
        file: String,
        close_after: bool,
        respond: SyncSender<Result<Value>>,
    },
    Close {
        file: String,
    },
    Ping {
        respond: SyncSender<()>,
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

// ---------------------------------------------------------------------------
// Coordinator: single thread owning all state, no locks
// ---------------------------------------------------------------------------

/// A file check waiting for LSP completion signals.
struct PendingCheck {
    filepath: String,
    t0: Instant,
    close_after: bool,
    respond: SyncSender<Result<Value>>,
}

/// A check request waiting for a concurrency slot.
struct QueuedCheck {
    file: String,
    close_after: bool,
    respond: SyncSender<Result<Value>>,
}

struct Coordinator {
    project_root: PathBuf,
    cmd_rx: Receiver<Cmd>,
    cmd_tx: Sender<Cmd>,
    ready_tx: Option<SyncSender<()>>,
    lsp_stdin: Option<ChildStdin>,
    lake_pid: Option<u32>,
    _watcher: Option<RecommendedWatcher>,
    next_lsp_id: u64,
    diagnostics: HashMap<String, Vec<Value>>,
    progress_done: HashMap<String, bool>,
    diagnostics_received: HashMap<String, bool>,
    /// URI -> pending checks waiting for completion
    pending_checks: HashMap<String, Vec<PendingCheck>>,
    opened_files: HashMap<String, u64>,
    changed_files: HashSet<String>,
    layout_changed: bool,
    /// Max number of files checked concurrently by the LSP server
    max_concurrent: usize,
    /// Number of checks currently in flight
    active_count: usize,
    /// Checks waiting for a concurrency slot
    check_queue: VecDeque<QueuedCheck>,
    /// Socket path for cleanup on shutdown
    sock_path: String,
    /// PID file path for cleanup on shutdown
    pid_path: String,
}

impl Coordinator {
    fn new(
        project_root: PathBuf,
        cmd_rx: Receiver<Cmd>,
        cmd_tx: Sender<Cmd>,
        ready_tx: SyncSender<()>,
        sock_path: String,
        pid_path: String,
    ) -> Self {
        let max_concurrent = env::var("LEAN_DAEMON_JOBS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(|| {
                let cpus = thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4);
                // Each Lean worker is roughly single-threaded; cap at 8 to
                // limit memory usage (~200MB-3GB per worker)
                cpus.min(8)
            });

        Coordinator {
            project_root,
            cmd_rx,
            cmd_tx,
            ready_tx: Some(ready_tx),
            lsp_stdin: None,
            lake_pid: None,
            _watcher: None,
            next_lsp_id: 1,
            diagnostics: HashMap::new(),
            progress_done: HashMap::new(),
            diagnostics_received: HashMap::new(),
            pending_checks: HashMap::new(),
            opened_files: HashMap::new(),
            changed_files: HashSet::new(),
            layout_changed: false,
            max_concurrent,
            active_count: 0,
            check_queue: VecDeque::new(),
            sock_path,
            pid_path,
        }
    }

    fn run(mut self) {
        if let Err(e) = self.start_lake_serve() {
            eprintln!("[lean-daemon] Failed to start: {e}");
            process::exit(1);
        }

        // Signal main thread that we're ready to accept commands
        if let Some(tx) = self.ready_tx.take() {
            let _ = tx.send(());
        }

        loop {
            match self.cmd_rx.recv() {
                Ok(cmd) => self.handle_cmd(cmd),
                Err(_) => break,
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
                    self.check_queue.push_back(QueuedCheck { file, close_after, respond });
                }
            }
            Cmd::Close { file } => {
                self.close_file(&file);
            }
            Cmd::Ping { respond } => {
                let _ = respond.send(());
            }
            Cmd::Shutdown { respond } => {
                let _ = respond.send(());
                self.shutdown();
                let _ = fs::remove_file(&self.sock_path);
                let _ = fs::remove_file(&self.pid_path);
                eprintln!("[lean-daemon] Clean shutdown complete");
                process::exit(0);
            }
            Cmd::LspMessage(msg) => {
                self.handle_lsp_message(msg);
            }
            Cmd::FileChanged(relpath) => {
                self.changed_files.insert(relpath);
            }
            Cmd::LayoutChanged => {
                self.layout_changed = true;
            }
            Cmd::LspCrashed => {
                self.handle_lsp_crash();
            }
        }
    }

    // -- Lake serve lifecycle -----------------------------------------------

    fn start_lake_serve(&mut self) -> Result<()> {
        eprintln!("[lean-daemon] Building CertCheck shared lib...");
        let _ = Command::new("lake")
            .args(["build", "CertCheck:shared"])
            .current_dir(&self.project_root)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();

        let certcheck_lib = self.project_root.join(".lake/build/lib/libaks_CertCheck.so");
        let plugin_arg = format!("--plugin={}", certcheck_lib.to_string_lossy());

        eprintln!("[lean-daemon] Starting lake serve in {}...", self.project_root.display());
        let mut proc = Command::new("lake")
            .args(["serve", "--", &plugin_arg])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .current_dir(&self.project_root)
            .process_group(0) // Own process group so shutdown kills lean workers too
            .spawn()?;

        self.lsp_stdin = proc.stdin.take();
        let stdout = proc.stdout.take().ok_or(DaemonError::Other("No stdout".into()))?;
        self.lake_pid = Some(proc.id());

        // Reset state
        self.next_lsp_id = 1;
        self.diagnostics.clear();
        self.progress_done.clear();
        self.diagnostics_received.clear();
        // Error out any pending/queued checks from before restart
        for (_, checks) in self.pending_checks.drain() {
            for check in checks {
                let _ = check.respond.send(Err(DaemonError::ServerRestarted));
            }
        }
        for queued in self.check_queue.drain(..) {
            let _ = queued.respond.send(Err(DaemonError::ServerRestarted));
        }
        self.active_count = 0;
        self.opened_files.clear();
        self.layout_changed = false;

        // Spawn LSP reader thread
        let tx = self.cmd_tx.clone();
        thread::Builder::new()
            .name("lsp-reader".into())
            .spawn(move || lsp_reader_thread(tx, stdout))?;

        // Monitor thread: detects lake serve death (even if lean --server
        // keeps the pipe open, which prevents the reader from seeing EOF).
        let tx = self.cmd_tx.clone();
        thread::Builder::new()
            .name("lake-monitor".into())
            .spawn(move || {
                let _ = proc.wait();
                let _ = tx.send(Cmd::LspCrashed);
            })?;

        // Send initialize request and wait for response
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

        // Drain command channel until we get the initialize response
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(DaemonError::Timeout { operation: "initialize", seconds: 60 });
            }
            match self.cmd_rx.recv_timeout(remaining) {
                Ok(Cmd::LspMessage(msg)) => {
                    if msg.get("id").and_then(|v| v.as_u64()) == Some(init_id) {
                        break; // Got initialize response
                    }
                    self.handle_lsp_message(msg);
                }
                // Handle other commands that may arrive during init
                Ok(Cmd::FileChanged(p)) => { self.changed_files.insert(p); }
                Ok(Cmd::LayoutChanged) => {}
                Ok(Cmd::Ping { respond }) => { let _ = respond.send(()); }
                Ok(Cmd::Close { .. }) => {}
                Ok(Cmd::Check { respond, .. }) => {
                    let _ = respond.send(Err(DaemonError::ServerInitializing));
                }
                Ok(Cmd::LspCrashed) => {} // Stale from old reader after restart, ignore
                Ok(Cmd::Shutdown { respond }) => {
                    let _ = respond.send(());
                    self.shutdown();
                    process::exit(0);
                }
                Err(_) => return Err(DaemonError::Timeout { operation: "initialize", seconds: 60 }),
            }
        }

        self.lsp_notify("initialized", serde_json::json!({}))?;
        eprintln!(
            "[lean-daemon] Initialized in {:.1}s (max {} concurrent checks)",
            t0.elapsed().as_secs_f64(),
            self.max_concurrent,
        );

        // Start file watcher
        self._watcher = start_watcher(&self.project_root, self.cmd_tx.clone());
        if self._watcher.is_some() {
            eprintln!("[lean-daemon] File watcher started (inotify)");
        } else {
            eprintln!("[lean-daemon] Warning: file watcher failed to start");
        }

        Ok(())
    }

    fn shutdown(&mut self) {
        // Try graceful LSP shutdown (fire-and-forget)
        let shutdown_id = self.next_lsp_id;
        self.next_lsp_id += 1;
        let _ = self.lsp_send_raw(&serde_json::to_vec(&serde_json::json!({
            "jsonrpc": "2.0",
            "id": shutdown_id,
            "method": "shutdown",
            "params": {},
        })).unwrap());
        let _ = self.lsp_notify("exit", serde_json::json!({}));

        self.lsp_stdin = None;
        if let Some(pid) = self.lake_pid.take() {
            // Kill entire process group (lake serve + lean workers).
            // lake serve is spawned with process_group(0) so its children
            // (lean --server, lean --worker) share its pgid.
            unsafe { libc::kill(-(pid as i32), libc::SIGKILL); }
            // Monitor thread reaps the process via Child::wait()
            thread::sleep(Duration::from_millis(100));
        }
        self._watcher = None;
    }

    fn restart_if_stale(&mut self) {
        if !self.layout_changed {
            return;
        }
        eprintln!("[lean-daemon] File layout changed, restarting lake serve...");
        self.shutdown();
        if let Err(e) = self.start_lake_serve() {
            eprintln!("[lean-daemon] Failed to restart: {e}");
        }
    }

    fn handle_lsp_crash(&mut self) {
        eprintln!("[lean-daemon] lake serve crashed, failing in-flight checks and restarting...");
        for (_, checks) in self.pending_checks.drain() {
            for check in checks {
                let _ = check.respond.send(Err(DaemonError::ServerRestarted));
            }
        }
        for queued in self.check_queue.drain(..) {
            let _ = queued.respond.send(Err(DaemonError::ServerRestarted));
        }
        self.active_count = 0;
        self.shutdown();
        if let Err(e) = self.start_lake_serve() {
            eprintln!("[lean-daemon] Failed to restart after crash: {e}");
        }
    }

    // -- LSP I/O (direct writes, no locks) ----------------------------------

    fn lsp_send_raw(&mut self, body: &[u8]) -> Result<()> {
        let stdin = self.lsp_stdin.as_mut().ok_or(DaemonError::LspNotStarted)?;
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
                        self.diagnostics.insert(uri.clone(), diags);
                        self.diagnostics_received.insert(uri.clone(), true);
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
                            self.progress_done.insert(uri.clone(), true);
                            self.try_signal_completion(&uri);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn try_signal_completion(&mut self, uri: &str) {
        if !self.progress_done.get(uri).copied().unwrap_or(false)
            || !self.diagnostics_received.get(uri).copied().unwrap_or(false)
        {
            return;
        }

        if let Some(checks) = self.pending_checks.remove(uri) {
            let diagnostics = self.diagnostics.get(uri).cloned().unwrap_or_default();
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
                self.close_file(&filepath);
            }

            // Free a concurrency slot and start queued checks
            self.active_count = self.active_count.saturating_sub(1);
            self.drain_queue();
        }
    }

    fn drain_queue(&mut self) {
        while self.active_count < self.max_concurrent {
            if let Some(queued) = self.check_queue.pop_front() {
                self.active_count += 1;
                self.start_check(&queued.file, queued.close_after, queued.respond);
            } else {
                break;
            }
        }
    }

    // -- File operations ----------------------------------------------------

    fn file_uri(&self, filepath: &str) -> (PathBuf, String) {
        let abspath = if filepath.starts_with('/') {
            PathBuf::from(filepath)
        } else {
            self.project_root.join(filepath)
        };
        let uri = path_to_uri(&abspath);
        (abspath, uri)
    }

    fn sync_changed_files(&mut self, target_uri: &str) {
        let changed: Vec<String> = self.changed_files.drain().collect();
        if changed.is_empty() {
            return;
        }

        let mut watched_changes = Vec::new();

        for relpath in &changed {
            let abspath = self.project_root.join(relpath);
            let uri = path_to_uri(&abspath);
            if uri == target_uri {
                continue;
            }

            if self.opened_files.contains_key(&uri) {
                if let Ok(content) = fs::read_to_string(&abspath) {
                    let v = self.opened_files.get_mut(&uri).unwrap();
                    *v += 1;
                    let version = *v;
                    let _ = self.lsp_notify(
                        "textDocument/didChange",
                        serde_json::json!({
                            "textDocument": {"uri": uri, "version": version},
                            "contentChanges": [{"text": content}],
                        }),
                    );
                }
            } else {
                watched_changes.push(serde_json::json!({"uri": uri, "type": 2}));
            }
        }

        if !watched_changes.is_empty() {
            let _ = self.lsp_notify(
                "workspace/didChangeWatchedFiles",
                serde_json::json!({"changes": watched_changes}),
            );
        }
    }

    /// Begin a file check: sync dependencies, send didOpen/didChange, register
    /// completion callback. Does NOT block — the result is sent on `respond`
    /// when LSP completion signals arrive (or the client handler times out).
    fn start_check(
        &mut self,
        filepath: &str,
        close_after: bool,
        respond: SyncSender<Result<Value>>,
    ) {
        let (abspath, uri) = self.file_uri(filepath);

        self.sync_changed_files(&uri);

        let content = match fs::read_to_string(&abspath) {
            Ok(c) => c,
            Err(e) => {
                let _ = respond.send(Err(DaemonError::Io(e)));
                self.active_count = self.active_count.saturating_sub(1);
                self.drain_queue();
                return;
            }
        };

        let t0 = Instant::now();

        // Reset completion tracking
        self.progress_done.insert(uri.clone(), false);
        self.diagnostics_received.insert(uri.clone(), false);
        self.diagnostics.remove(&uri);

        // Send didOpen or didChange
        let send_result = if self.opened_files.contains_key(&uri) {
            let v = self.opened_files.get_mut(&uri).unwrap();
            *v += 1;
            let version = *v;
            self.lsp_notify(
                "textDocument/didChange",
                serde_json::json!({
                    "textDocument": {"uri": uri, "version": version},
                    "contentChanges": [{"text": content}],
                }),
            )
        } else {
            self.opened_files.insert(uri.clone(), 1);
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
            let _ = respond.send(Err(e));
            self.active_count = self.active_count.saturating_sub(1);
            self.drain_queue();
            return;
        }

        // Register pending check — completion is signaled by try_signal_completion
        // when both fileProgress:[] and publishDiagnostics arrive
        self.pending_checks
            .entry(uri)
            .or_default()
            .push(PendingCheck {
                filepath: filepath.to_string(),
                t0,
                close_after,
                respond,
            });
    }

    fn close_file(&mut self, filepath: &str) {
        let (_, uri) = self.file_uri(filepath);
        if self.opened_files.remove(&uri).is_some() {
            let _ = self.lsp_notify(
                "textDocument/didClose",
                serde_json::json!({"textDocument": {"uri": uri}}),
            );
        }
    }
}

// ---------------------------------------------------------------------------
// LSP reader thread
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// File watcher
// ---------------------------------------------------------------------------

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
    for dir in &["AKS", "Bench"] {
        let d = project_root.join(dir);
        if d.is_dir() {
            let _ = watcher.watch(&d, RecursiveMode::Recursive);
        }
    }

    Some(watcher)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn project_hash(root: &Path) -> String {
    let mut hasher = Md5::new();
    hasher.update(root.to_string_lossy().as_bytes());
    let result = hasher.finalize();
    format!("{:02x}{:02x}{:02x}{:02x}", result[0], result[1], result[2], result[3])
}

fn socket_path(hash: &str) -> String {
    format!("/tmp/lean-daemon-{}.sock", hash)
}

fn pid_path(hash: &str) -> String {
    format!("/tmp/lean-daemon-{}.pid", hash)
}

fn path_to_uri(path: &Path) -> String {
    format!("file://{}", path.to_string_lossy())
}

// ---------------------------------------------------------------------------
// Socket server + main
// ---------------------------------------------------------------------------

fn handle_client(cmd_tx: &Sender<Cmd>, mut stream: UnixStream) {
    let result: Result<String> = (|| {
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

        let request: Value = serde_json::from_slice(&data)?;
        let command = request.get("command").and_then(|v| v.as_str()).unwrap_or("");

        match command {
            "check" => {
                let file = request.get("file").and_then(|v| v.as_str())
                    .ok_or(DaemonError::MissingField("file"))?;
                let close_after = request.get("close_after").and_then(|v| v.as_bool())
                    .unwrap_or(false);
                let (tx, rx) = mpsc::sync_channel(1);
                cmd_tx.send(Cmd::Check {
                    file: file.to_string(),
                    close_after,
                    respond: tx,
                }).map_err(|_| DaemonError::CoordinatorDead)?;
                // Block until coordinator signals completion (or timeout).
                // 600s accommodates queue wait + check time for large files.
                let result = rx.recv_timeout(Duration::from_secs(600))
                    .map_err(|_| DaemonError::Timeout { operation: "file check", seconds: 600 })??;
                Ok(serde_json::to_string(&result)?)
            }
            "close" => {
                let file = request.get("file").and_then(|v| v.as_str())
                    .ok_or(DaemonError::MissingField("file"))?;
                cmd_tx.send(Cmd::Close { file: file.to_string() })
                    .map_err(|_| DaemonError::CoordinatorDead)?;
                Ok(r#"{"status":"closed"}"#.to_string())
            }
            "ping" => {
                let (tx, rx) = mpsc::sync_channel(1);
                cmd_tx.send(Cmd::Ping { respond: tx })
                    .map_err(|_| DaemonError::CoordinatorDead)?;
                let _ = rx.recv();
                Ok(r#"{"status":"ok"}"#.to_string())
            }
            "shutdown" => {
                let (tx, rx) = mpsc::sync_channel(1);
                let _ = cmd_tx.send(Cmd::Shutdown { respond: tx });
                let _ = rx.recv();
                Ok(r#"{"status":"shutting_down"}"#.to_string())
            }
            _ => Ok(format!(r#"{{"error":"Unknown command: {}"}}"#, command)),
        }
    })();

    match result {
        Ok(response) => { let _ = stream.write_all(response.as_bytes()); }
        Err(e) => {
            let r = serde_json::json!({"error": e.to_string()});
            let _ = stream.write_all(serde_json::to_string(&r).unwrap().as_bytes());
        }
    }
    let _ = stream.flush();
}

/// Write end of self-pipe for signal notification.
static SIGNAL_PIPE_WR: AtomicI32 = AtomicI32::new(-1);

extern "C" fn signal_handler(_sig: libc::c_int) {
    let fd = SIGNAL_PIPE_WR.load(Ordering::SeqCst);
    if fd >= 0 {
        unsafe { libc::write(fd, b"x".as_ptr() as *const libc::c_void, 1); }
    }
}

fn main() {
    let project_root = env::var("PROJECT_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| env::current_dir().unwrap_or_else(|_| PathBuf::from(".")));

    let hash = project_hash(&project_root);
    let sock_path = socket_path(&hash);
    let pid_file = pid_path(&hash);
    let _ = fs::remove_file(&sock_path);

    // Self-pipe for signal notification: signal handler writes a byte,
    // poll() wakes up immediately. Zero latency, zero idle CPU.
    let mut pipe_fds = [0i32; 2];
    unsafe {
        if libc::pipe(pipe_fds.as_mut_ptr()) != 0 {
            eprintln!("[lean-daemon] Failed to create signal pipe");
            process::exit(1);
        }
        // Non-blocking write end so signal handler never blocks
        let flags = libc::fcntl(pipe_fds[1], libc::F_GETFL);
        libc::fcntl(pipe_fds[1], libc::F_SETFL, flags | libc::O_NONBLOCK);
    }
    let signal_read_fd = pipe_fds[0];
    SIGNAL_PIPE_WR.store(pipe_fds[1], Ordering::SeqCst);

    unsafe {
        libc::signal(libc::SIGTERM, signal_handler as *const () as libc::sighandler_t);
        libc::signal(libc::SIGINT, signal_handler as *const () as libc::sighandler_t);
    }

    let (cmd_tx, cmd_rx) = mpsc::channel();
    let (ready_tx, ready_rx) = mpsc::sync_channel(1);

    // Spawn coordinator thread
    let coord = Coordinator::new(
        project_root, cmd_rx, cmd_tx.clone(), ready_tx,
        sock_path.clone(), pid_file.clone(),
    );
    thread::Builder::new()
        .name("coordinator".into())
        .spawn(move || coord.run())
        .expect("Failed to spawn coordinator");

    // Wait for coordinator to finish initialization
    if ready_rx.recv_timeout(Duration::from_secs(120)).is_err() {
        eprintln!("[lean-daemon] Coordinator failed to start within 120s");
        process::exit(1);
    }

    // Write our PID (overwrites lean-check's cargo PID with the actual daemon PID)
    let _ = fs::write(&pid_file, process::id().to_string());

    // Bind socket
    let listener = match UnixListener::bind(&sock_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("[lean-daemon] Failed to bind socket {sock_path}: {e}");
            process::exit(1);
        }
    };
    eprintln!("[lean-daemon] Listening on {sock_path}");

    // poll() on listener + signal pipe: blocks until a connection or signal arrives
    let listener_fd = listener.as_raw_fd();
    let mut pollfds = [
        libc::pollfd { fd: listener_fd, events: libc::POLLIN, revents: 0 },
        libc::pollfd { fd: signal_read_fd, events: libc::POLLIN, revents: 0 },
    ];

    loop {
        pollfds[0].revents = 0;
        pollfds[1].revents = 0;
        let ret = unsafe { libc::poll(pollfds.as_mut_ptr(), 2, -1) };
        if ret < 0 {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::Interrupted {
                continue; // EINTR — re-poll, signal pipe will be readable
            }
            eprintln!("[lean-daemon] poll error: {err}");
            break;
        }

        // Signal received — shut down
        if pollfds[1].revents & libc::POLLIN != 0 {
            eprintln!("[lean-daemon] Signal received, shutting down...");
            let (tx, rx) = mpsc::sync_channel(1);
            let _ = cmd_tx.send(Cmd::Shutdown { respond: tx });
            // Coordinator handles cleanup and calls process::exit(0).
            // This recv is a fallback in case the coordinator is stuck.
            let _ = rx.recv_timeout(Duration::from_secs(5));
            let _ = fs::remove_file(&sock_path);
            let _ = fs::remove_file(&pid_file);
            process::exit(0);
        }

        // Connection ready
        if pollfds[0].revents & libc::POLLIN != 0 {
            match listener.accept() {
                Ok((stream, _)) => {
                    let tx = cmd_tx.clone();
                    thread::Builder::new()
                        .name("client".into())
                        .spawn(move || handle_client(&tx, stream))
                        .ok();
                }
                Err(e) => eprintln!("[lean-daemon] Accept error: {e}"),
            }
        }
    }
}
