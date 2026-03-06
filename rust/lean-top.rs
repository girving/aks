#!/usr/bin/env -S cargo +nightly -Zscript
---cargo
[dependencies]
libc = "0.2"

# cargo-script defaults to the dev profile; opt-level=2 keeps the TUI responsive.
[profile.dev]
opt-level = 2
overflow-checks = false
debug = false

[profile.release]
opt-level = 3
---

//! Minimal process monitor for lean/lake/certificate builds.
//! Works on Linux (via /proc) and macOS (via sysctl + libproc).
//! Designed for narrow terminals (~69 cols).

use std::collections::{HashMap, HashSet};
use std::io::{self, Read as _, Write};
use std::os::unix::io::AsRawFd;
use std::path::Path;
use std::time::{Duration, Instant};

const CPU_THRESH: f64 = 5.0;     // show if CPU% >= this
const MEM_MB_THRESH: u64 = 128;  // show if RSS >= this MB

// ── Terminal ─────────────────────────────────────────────────────────────────

fn term_width() -> usize {
    unsafe {
        let mut ws: libc::winsize = std::mem::zeroed();
        if libc::ioctl(libc::STDOUT_FILENO, libc::TIOCGWINSZ, &mut ws) == 0 && ws.ws_col > 0 {
            ws.ws_col as usize
        } else {
            80
        }
    }
}

// ── Tree layout ──────────────────────────────────────────────────────────────

/// Flatten process list into tree order with indentation prefixes.
/// Returns (prefix_string, proc_index) pairs in display order.
fn tree_layout(procs: &[ProcInfo]) -> Vec<(String, usize)> {
    let pid_set: HashSet<u32> = procs.iter().map(|p| p.pid).collect();

    // Map pid → index in procs
    let mut pid_to_idx: HashMap<u32, usize> = HashMap::new();
    for (i, p) in procs.iter().enumerate() {
        pid_to_idx.insert(p.pid, i);
    }

    // Map ppid → children indices (only parents that are in our list)
    let mut children: HashMap<u32, Vec<usize>> = HashMap::new();
    let mut roots: Vec<usize> = Vec::new();
    for (i, p) in procs.iter().enumerate() {
        if pid_set.contains(&p.ppid) {
            children.entry(p.ppid).or_default().push(i);
        } else {
            roots.push(i);
        }
    }

    // Sort children by PID for stable display
    for kids in children.values_mut() {
        kids.sort_by_key(|&i| procs[i].pid);
    }
    roots.sort_by_key(|&i| procs[i].pid);

    let mut result = Vec::new();
    for &root in &roots {
        tree_walk(procs, &children, root, "", true, true, &mut result);
    }
    result
}

fn tree_walk(
    procs: &[ProcInfo],
    children: &HashMap<u32, Vec<usize>>,
    idx: usize,
    prefix: &str,
    is_last: bool,
    is_root: bool,
    out: &mut Vec<(String, usize)>,
) {
    let connector = if is_root {
        String::new()
    } else if is_last {
        format!("{prefix}└─")
    } else {
        format!("{prefix}├─")
    };
    out.push((connector, idx));

    let child_prefix = if is_root {
        String::new()
    } else if is_last {
        format!("{prefix}  ")
    } else {
        format!("{prefix}│ ")
    };

    if let Some(kids) = children.get(&procs[idx].pid) {
        for (i, &kid) in kids.iter().enumerate() {
            let last = i == kids.len() - 1;
            tree_walk(procs, children, kid, &child_prefix, last, false, out);
        }
    }
}

// ── Entry point ───────────────────────────────────────────────────────────────

fn main() {
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as u64;
    let clock_ticks = unsafe { libc::sysconf(libc::_SC_CLK_TCK) } as f64;
    let num_cpus = std::thread::available_parallelism()
        .map(|n| n.get() as f64)
        .unwrap_or(1.0);

    // Raw mode so 'q' quits without Enter
    let stdin_fd = io::stdin().as_raw_fd();
    let orig_termios = unsafe {
        let mut t: libc::termios = std::mem::zeroed();
        libc::tcgetattr(stdin_fd, &mut t);
        t
    };
    let _guard = RawModeGuard { fd: stdin_fd, orig: orig_termios };
    unsafe {
        let mut raw = orig_termios;
        raw.c_lflag &= !(libc::ICANON | libc::ECHO);
        raw.c_cc[libc::VMIN] = 0;
        raw.c_cc[libc::VTIME] = 0;
        libc::tcsetattr(stdin_fd, libc::TCSANOW, &raw);
    }

    print!("\x1b[?25l"); // hide cursor
    let mut prev_times: HashMap<u32, (u64, Instant)> = HashMap::new();
    let boot = boot_time();

    loop {
        let wall_now = now_epoch();
        let width = term_width();
        let mut procs = collect_procs(page_size, clock_ticks, boot, wall_now, &mut prev_times);
        procs.sort_by_key(|p| p.pid);

        let mut out = io::stdout().lock();
        write!(out, "\x1b[H").ok();

        let now_str = format_time();
        let (load_str, load_frac) = load_avg(num_cpus);
        let (mem_str, mem_frac) = mem_info();
        let (lr, _, lb) = frac_color(0.0, load_frac);
        let (mr, _, mb) = frac_color(mem_frac, 0.0);
        line(&mut out, &format!("\x1b[1mlean-top\x1b[0m  {now_str}"));
        line(&mut out, &format!(
            "\x1b[38;2;0;0;255mload:\x1b[0m \x1b[38;2;{lr};0;{lb}m{load_str}\x1b[0m  \
             \x1b[38;2;255;0;0mmem:\x1b[0m \x1b[38;2;{mr};0;{mb}m{mem_str}\x1b[0m"
        ));
        line(&mut out, &"─".repeat(width));
        line(&mut out, &format!(
            "\x1b[1m{:<6} {:>6} {:>6} {:>6}  {}\x1b[0m", "PID", "CPU%", "RSS", "AGE", "COMMAND"
        ));
        line(&mut out, &"─".repeat(width));

        if procs.is_empty() {
            line(&mut out, "(no matching processes)");
        }
        let tree = tree_layout(&procs);
        for (prefix, idx) in &tree {
            let p = &procs[*idx];
            let cpu_str = format!("{:6.1}", p.cpu);
            let rss_str = format_mem(p.rss_bytes);
            let age_str = format_age(p.age_secs);
            let stats_width = 6 + 1 + 6 + 1 + 6 + 1 + 6 + 2; // PID + spaces + CPU + RSS + AGE + gap
            let prefix_width = prefix.chars().count();
            let cmd_width = width.saturating_sub(stats_width + prefix_width);
            let cmd = truncate(&p.display, cmd_width);
            let text = format!(
                "{:<6} {:>6} {:>6} {:>6}  {prefix}{cmd}",
                p.pid, cpu_str, rss_str, age_str
            );
            let (r, g, b) = row_color(p.cpu, p.rss_bytes);
            line(&mut out, &format!("\x1b[38;2;{r};{g};{b}m{text}\x1b[0m"));
        }

        write!(out, "\x1b[J").ok();
        out.flush().ok();
        drop(out);

        // Poll for 'q' over the 2s sleep (check every 50ms)
        for _ in 0..40 {
            let mut buf = [0u8; 1];
            if io::stdin().read(&mut buf).unwrap_or(0) == 1 && buf[0] == b'q' {
                return;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}

// ── Terminal restore guard ────────────────────────────────────────────────────

struct RawModeGuard { fd: i32, orig: libc::termios }
impl Drop for RawModeGuard {
    fn drop(&mut self) {
        unsafe { libc::tcsetattr(self.fd, libc::TCSANOW, &self.orig) };
        print!("\x1b[?25h"); // show cursor
        let _ = io::stdout().flush();
    }
}

fn line(out: &mut impl Write, s: &str) {
    write!(out, "{s}\x1b[K\n").ok();
}

// ── Process info struct ───────────────────────────────────────────────────────

struct ProcInfo {
    pid: u32,
    ppid: u32,
    cpu: f64,
    rss_bytes: u64,
    age_secs: u64,
    display: String,
}

// ── Wall clock ────────────────────────────────────────────────────────────────

fn now_epoch() -> u64 {
    let mut tv: libc::timeval = unsafe { std::mem::zeroed() };
    unsafe { libc::gettimeofday(&mut tv, std::ptr::null_mut()) };
    tv.tv_sec as u64
}

// ── Boot time ─────────────────────────────────────────────────────────────────

#[cfg(target_os = "linux")]
fn boot_time() -> u64 {
    let Ok(content) = std::fs::read_to_string("/proc/stat") else { return 0 };
    for line in content.lines() {
        if let Some(rest) = line.strip_prefix("btime ") {
            return rest.trim().parse().unwrap_or(0);
        }
    }
    0
}

#[cfg(target_os = "macos")]
fn boot_time() -> u64 {
    unsafe {
        let mut mib = [libc::CTL_KERN, libc::KERN_BOOTTIME];
        let mut tv: libc::timeval = std::mem::zeroed();
        let mut size = std::mem::size_of::<libc::timeval>();
        libc::sysctl(
            mib.as_mut_ptr(), 2,
            &mut tv as *mut _ as *mut libc::c_void,
            &mut size,
            std::ptr::null_mut(), 0,
        );
        tv.tv_sec as u64
    }
}

// ── macOS FFI declarations ────────────────────────────────────────────────────

#[cfg(target_os = "macos")]
mod mac_sys {
    unsafe extern "C" {
        /// Returns count of PIDs; pass null/0 to query required buffer size.
        pub fn proc_listallpids(buffer: *mut libc::c_void, buffersize: libc::c_int) -> libc::c_int;
        /// Copies up to buffersize bytes of process name into buffer.
        pub fn proc_name(pid: libc::c_int, buffer: *mut libc::c_void, buffersize: u32) -> libc::c_int;
        /// Generic proc info call; flavor selects the info type.
        pub fn proc_pidinfo(
            pid: libc::c_int, flavor: libc::c_int, arg: u64,
            buffer: *mut libc::c_void, buffersize: libc::c_int,
        ) -> libc::c_int;
        pub fn mach_host_self() -> libc::c_uint;
        pub fn host_statistics64(
            host: libc::c_uint, flavor: libc::c_int,
            info: *mut libc::c_int, count: *mut libc::c_uint,
        ) -> libc::c_int;
    }

    pub const PROC_PIDTASKINFO: i32 = 4;
    pub const PROC_PIDTBSDINFO: i32 = 3;
    pub const HOST_VM_INFO64: i32 = 4;

    /// Mirror of `struct proc_taskinfo` from <sys/proc_info.h>.
    /// pti_resident_size is in bytes; pti_total_{user,system} in nanoseconds.
    #[repr(C)]
    pub struct ProcTaskInfo {
        pub pti_virtual_size:   u64,
        pub pti_resident_size:  u64,
        pub pti_total_user:     u64,
        pub pti_total_system:   u64,
        pub pti_threads_user:   u64,
        pub pti_threads_system: u64,
        pub pti_policy:             i32,
        pub pti_faults:             i32,
        pub pti_pageins:            i32,
        pub pti_cow_faults:         i32,
        pub pti_messages_sent:      i32,
        pub pti_messages_received:  i32,
        pub pti_syscalls_mach:      i32,
        pub pti_syscalls_unix:      i32,
        pub pti_csw:                i32,
        pub pti_threadnum:          i32,
        pub pti_numrunning:         i32,
        pub pti_priority:           i32,
    }
}

// ── Process collection: macOS ─────────────────────────────────────────────────

#[cfg(target_os = "macos")]
fn collect_procs(
    _page_size: u64,
    _clock_ticks: f64,
    _boot: u64,
    wall_now: u64,
    prev_times: &mut HashMap<u32, (u64, Instant)>,
) -> Vec<ProcInfo> {
    use mac_sys::*;
    let now = Instant::now();
    let mut result = Vec::new();
    let mut seen_pids = HashSet::new();
    let my_pid = std::process::id();

    // Query required buffer size, then get all PIDs.
    let capacity = unsafe { proc_listallpids(std::ptr::null_mut(), 0) };
    if capacity <= 0 { return result; }
    let mut pids = vec![0i32; capacity as usize + 32];
    let count = unsafe {
        proc_listallpids(
            pids.as_mut_ptr() as *mut libc::c_void,
            (pids.len() * std::mem::size_of::<i32>()) as i32,
        )
    };
    if count <= 0 { return result; }
    pids.truncate(count as usize);

    for pid in pids {
        let pid_u = pid as u32;
        if pid <= 0 || pid_u == my_pid { continue; }
        seen_pids.insert(pid_u);

        // Task info: RSS (bytes) + CPU time (nanoseconds).
        let mut ti: ProcTaskInfo = unsafe { std::mem::zeroed() };
        let ret = unsafe {
            proc_pidinfo(
                pid, PROC_PIDTASKINFO, 0,
                &mut ti as *mut _ as *mut libc::c_void,
                std::mem::size_of::<ProcTaskInfo>() as i32,
            )
        };
        if ret <= 0 { continue; }

        let rss_bytes = ti.pti_resident_size;
        let total_ns = ti.pti_total_user + ti.pti_total_system;
        let rss_mb = rss_bytes / (1024 * 1024);

        // CPU% = ΔCPU_ns / (Δwall_s * 1e9) * 100  (100% = one core)
        let cpu = match prev_times.get(&pid_u) {
            Some(&(prev_ns, prev_instant)) => {
                let dt = now.duration_since(prev_instant).as_secs_f64();
                if dt > 0.01 {
                    (total_ns.saturating_sub(prev_ns) as f64 / 1e9 / dt) * 100.0
                } else { 0.0 }
            }
            None => 0.0,
        };
        prev_times.insert(pid_u, (total_ns, now));

        // Short process name.
        let comm = unsafe {
            let mut buf = [0u8; 64];
            proc_name(pid, buf.as_mut_ptr() as *mut libc::c_void, buf.len() as u32);
            let end = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
            String::from_utf8_lossy(&buf[..end]).into_owned()
        };

        // Full argv via KERN_PROCARGS2.
        let args = macos_proc_args(pid as u32);

        // Process start time + PPID from proc_bsdinfo.
        let (age_secs, ppid) = macos_proc_age_ppid(pid, wall_now);

        let always_show = is_lean_or_lake(&comm, &args);
        let high_cpu = cpu >= CPU_THRESH;
        let high_mem = rss_mb >= MEM_MB_THRESH;
        if !always_show && !high_cpu && !high_mem { continue; }
        if is_noise(&comm, &args) { continue; }

        let is_related = always_show || is_lean_related(&comm, &args);
        let display = build_display(&comm, &args, is_related);
        result.push(ProcInfo { pid: pid_u, ppid, cpu, rss_bytes, age_secs, display });
    }

    prev_times.retain(|pid, _| seen_pids.contains(pid));
    result
}

/// Parse KERN_PROCARGS2 for a PID: returns [exec_path, argv0, argv1, ...].
#[cfg(target_os = "macos")]
fn macos_proc_args(pid: u32) -> Vec<String> {
    unsafe {
        let mut mib = [libc::CTL_KERN, libc::KERN_PROCARGS2, pid as i32];
        let mut size = 0usize;
        libc::sysctl(mib.as_mut_ptr(), 3, std::ptr::null_mut(), &mut size, std::ptr::null_mut(), 0);
        if size < 4 { return vec![]; }

        let mut buf = vec![0u8; size];
        let ret = libc::sysctl(
            mib.as_mut_ptr(), 3,
            buf.as_mut_ptr() as *mut libc::c_void,
            &mut size,
            std::ptr::null_mut(), 0,
        );
        if ret != 0 { return vec![]; }

        // Layout: [argc: i32] [exec_path\0] [null padding] [argv[0]\0] [argv[1]\0] ...
        let argc = i32::from_ne_bytes(buf[..4].try_into().unwrap_or([0; 4])).max(0) as usize;
        let mut strings: Vec<String> = Vec::new();
        let mut i = 4usize;

        while i < size && strings.len() <= argc {
            // After the exec_path, skip null padding before argv[0].
            if strings.len() == 1 {
                while i < size && buf[i] == 0 { i += 1; }
            }
            let start = i;
            while i < size && buf[i] != 0 { i += 1; }
            if i > start {
                strings.push(String::from_utf8_lossy(&buf[start..i]).into_owned());
            }
            i += 1;
        }
        // [0] = exec_path, [1..] = argv — drop env vars beyond argc+1 entries.
        strings.into_iter().take(argc + 1).collect()
    }
}

/// Get process age in seconds + PPID via PROC_PIDTBSDINFO.
/// struct proc_bsdinfo: pbi_ppid (u32) at byte offset 16,
///                      pbi_start_tvsec (u64) at byte offset 120.
#[cfg(target_os = "macos")]
fn macos_proc_age_ppid(pid: i32, wall_now: u64) -> (u64, u32) {
    use mac_sys::*;
    const BUF_SIZE: i32 = 232; // PROC_PIDTBSDINFO_SIZE
    const PPID_OFF: usize = 16;  // offset of pbi_ppid in proc_bsdinfo
    const TVSEC_OFF: usize = 120; // offset of pbi_start_tvsec in proc_bsdinfo

    let mut buf = vec![0u8; BUF_SIZE as usize];
    let ret = unsafe {
        proc_pidinfo(pid, PROC_PIDTBSDINFO, 0,
                     buf.as_mut_ptr() as *mut libc::c_void, BUF_SIZE)
    };
    if ret < (TVSEC_OFF + 8) as i32 { return (0, 0); }
    let ppid = u32::from_ne_bytes(buf[PPID_OFF..PPID_OFF + 4].try_into().unwrap());
    let start = u64::from_ne_bytes(buf[TVSEC_OFF..TVSEC_OFF + 8].try_into().unwrap());
    (wall_now.saturating_sub(start), ppid)
}

// ── Process collection: Linux ─────────────────────────────────────────────────

#[cfg(target_os = "linux")]
fn collect_procs(
    page_size: u64,
    clock_ticks: f64,
    boot: u64,
    wall_now: u64,
    prev_times: &mut HashMap<u32, (u64, Instant)>,
) -> Vec<ProcInfo> {
    let now = Instant::now();
    let mut result = Vec::new();
    let mut seen_pids = HashSet::new();
    let my_pid = std::process::id();

    let Ok(entries) = std::fs::read_dir("/proc") else { return result };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        let Ok(pid) = name_str.parse::<u32>() else { continue };
        if pid == my_pid { continue }
        seen_pids.insert(pid);

        let proc_dir = format!("/proc/{pid}");
        let Ok(stat) = std::fs::read_to_string(format!("{proc_dir}/stat")) else { continue };
        let (comm, after_comm) = parse_stat(&stat);

        let cmdline = std::fs::read(format!("{proc_dir}/cmdline")).unwrap_or_default();
        let args: Vec<String> = cmdline
            .split(|&b| b == 0)
            .filter(|s| !s.is_empty())
            .map(|s| String::from_utf8_lossy(s).into_owned())
            .collect();

        let fields: Vec<&str> = after_comm.split_whitespace().collect();
        if fields.len() < 22 { continue }

        let ppid: u32 = fields[1].parse().unwrap_or(0);
        let utime: u64 = fields[11].parse().unwrap_or(0);
        let stime: u64 = fields[12].parse().unwrap_or(0);
        let total_ticks = utime + stime;
        let starttime: u64 = fields[19].parse().unwrap_or(0);
        let start_epoch = boot + starttime / clock_ticks as u64;
        let age_secs = wall_now.saturating_sub(start_epoch);
        let rss_pages: u64 = fields[21].parse().unwrap_or(0);
        let rss_bytes = rss_pages * page_size;
        let rss_mb = rss_bytes / (1024 * 1024);

        let cpu = match prev_times.get(&pid) {
            Some(&(prev_ticks, prev_instant)) => {
                let dt = now.duration_since(prev_instant).as_secs_f64();
                if dt > 0.01 {
                    (total_ticks.saturating_sub(prev_ticks) as f64
                        / clock_ticks / dt) * 100.0
                } else { 0.0 }
            }
            None => 0.0,
        };
        prev_times.insert(pid, (total_ticks, now));

        let always_show = is_lean_or_lake(&comm, &args);
        let high_cpu = cpu >= CPU_THRESH;
        let high_mem = rss_mb >= MEM_MB_THRESH;
        if !always_show && !high_cpu && !high_mem { continue }
        if is_noise(&comm, &args) { continue }

        let is_related = always_show || is_lean_related(&comm, &args);
        let display = build_display(&comm, &args, is_related);
        result.push(ProcInfo { pid, ppid, cpu, rss_bytes, age_secs, display });
    }

    prev_times.retain(|pid, _| seen_pids.contains(pid));
    result
}

#[cfg(target_os = "linux")]
fn parse_stat(stat: &str) -> (String, &str) {
    let open = stat.find('(').unwrap_or(0);
    let close = stat.rfind(')').unwrap_or(stat.len());
    let comm = stat[open + 1..close].to_string();
    let after = stat[close + 1..].trim_start();
    (comm, after)
}

// ── Load average (POSIX getloadavg — works on Linux and macOS) ───────────────

fn load_avg(num_cpus: f64) -> (String, f64) {
    let mut loads = [0.0f64; 3];
    let n = unsafe { libc::getloadavg(loads.as_mut_ptr(), 3) };
    if n >= 3 {
        let frac = (loads[0] / num_cpus).min(1.0);
        (format!("{:.2} {:.2} {:.2}", loads[0], loads[1], loads[2]), frac)
    } else {
        ("?".into(), 0.0)
    }
}

// ── Memory info ───────────────────────────────────────────────────────────────

#[cfg(target_os = "linux")]
fn mem_info() -> (String, f64) {
    let Ok(content) = std::fs::read_to_string("/proc/meminfo") else { return ("?".into(), 0.0) };
    let mut total = 0u64;
    let mut avail = 0u64;
    for line in content.lines() {
        if line.starts_with("MemTotal:") {
            total = line.split_whitespace().nth(1).and_then(|s| s.parse().ok()).unwrap_or(0);
        } else if line.starts_with("MemAvailable:") {
            avail = line.split_whitespace().nth(1).and_then(|s| s.parse().ok()).unwrap_or(0);
        }
    }
    let used = total.saturating_sub(avail);
    let frac = if total > 0 { used as f64 / total as f64 } else { 0.0 };
    (format!("{:.1}G / {:.1}G used",
             used as f64 / (1024.0 * 1024.0),
             total as f64 / (1024.0 * 1024.0)), frac)
}

/// macOS: total RAM from sysctl HW_MEMSIZE; free+inactive from host_statistics64.
/// vm_statistics64 starts with 4 natural_t (u32) fields: free, active, inactive, wire.
/// HOST_VM_INFO64_COUNT = sizeof(vm_statistics64_data_t)/sizeof(int) = 38.
#[cfg(target_os = "macos")]
fn mem_info() -> (String, f64) {
    use mac_sys::*;
    unsafe {
        // Total physical memory.
        let mut total: u64 = 0;
        let mut sz = std::mem::size_of::<u64>();
        let mut mib_hw = [libc::CTL_HW, libc::HW_MEMSIZE];
        libc::sysctl(mib_hw.as_mut_ptr(), 2,
                     &mut total as *mut _ as *mut libc::c_void, &mut sz,
                     std::ptr::null_mut(), 0);
        if total == 0 { return ("?".into(), 0.0); }

        // VM page stats: read as [u32; 38].
        // buf[0]=free_count, buf[1]=active_count, buf[2]=inactive_count (all natural_t=u32).
        let page = libc::sysconf(libc::_SC_PAGESIZE) as u64;
        let host = mach_host_self();
        let mut vm = [0u32; 38];
        let mut count = 38u32;
        let ret = host_statistics64(host, HOST_VM_INFO64,
                                    vm.as_mut_ptr() as *mut libc::c_int, &mut count);
        let avail = if ret == 0 { // KERN_SUCCESS
            (vm[0] as u64 + vm[2] as u64) * page  // free + inactive
        } else { 0 };

        let used = total.saturating_sub(avail);
        let frac = used as f64 / total as f64;
        (format!("{:.1}G / {:.1}G used",
                 used as f64 / (1u64 << 30) as f64,
                 total as f64 / (1u64 << 30) as f64), frac)
    }
}

// ── Process classification ────────────────────────────────────────────────────

fn is_noise(comm: &str, args: &[String]) -> bool {
    let name = args.first()
        .and_then(|a| Path::new(a).file_name())
        .map(|f| f.to_string_lossy().into_owned())
        .unwrap_or_else(|| comm.to_string());
    let name_lc = name.to_lowercase();

    // Google Chrome and its helpers
    if name_lc.contains("chrome") { return true; }

    // macOS UI widgets and system processes
    if name_lc.contains("widget") { return true; }

    // Bundle-ID style names (com.apple.*)
    if name.starts_with("com.apple.") { return true; }

    // Common macOS daemons / UI processes that clutter the display
    const NOISE: &[&str] = &[
        "amazon-cloudwatch-agent", "amazon-guardduty-agent", "ssm-session-worker",
        "spotlight", "springboard",
        "newstoday2", "newsscoringservice",
        "screentimeagent",
        "appleaccountd",
        "siriinferenced", "siriactionsd",
        "callservicesd",
        "calaccessd",
        "amsengagementd",
        "chronod",
        "remindd",
        "routined",
        "textunderstandingd",
        "corespeechd",
    ];
    if NOISE.contains(&name_lc.as_str()) { return true; }

    false
}

fn is_lean_or_lake(comm: &str, args: &[String]) -> bool {
    if comm == "lean" || comm == "lake" { return true }
    if let Some(arg0) = args.first() {
        let base = Path::new(arg0).file_name().map(|f| f.to_string_lossy()).unwrap_or_default();
        if base == "lean" || base == "lake" { return true }
    }
    false
}

fn is_lean_related(comm: &str, args: &[String]) -> bool {
    let comm_lower = comm.to_lowercase();
    for kw in &["lean", "lake", "certificate"] {
        if comm_lower.contains(kw) { return true }
    }
    for arg in args.iter().take(3) {
        let a = arg.to_lowercase();
        for kw in &["lean", "lake", "certificate"] {
            if a.contains(kw) { return true }
        }
    }
    false
}

fn build_display(comm: &str, args: &[String], is_related: bool) -> String {
    if !is_related {
        if let Some(arg0) = args.first() {
            return Path::new(arg0).file_name()
                .map(|f| f.to_string_lossy().into_owned())
                .unwrap_or_else(|| comm.to_string());
        }
        return comm.to_string();
    }
    let label = lean_label(args);
    match find_lean_file(args) {
        Some(f) => format!("{label} {f}"),
        None => label,
    }
}

fn lean_label(args: &[String]) -> String {
    let joined = args.join(" ").to_lowercase();
    if joined.contains("--worker") { return "lean".into() }
    if joined.contains("--server") { return "lean --server".into() }
    if joined.contains("lake") && joined.contains("serve") { return "lake serve".into() }
    if joined.contains("lean.rs") || joined.contains("debug/lean") { return "lean-mcp".into() }
    if joined.contains("certificate") { return "certificate".into() }
    for arg in args {
        let al = arg.to_lowercase();
        if ["lean", "lake", "certificate"].iter().any(|kw| al.contains(kw)) {
            return Path::new(arg).file_name()
                .map(|f| f.to_string_lossy().into_owned())
                .unwrap_or_else(|| arg.clone());
        }
    }
    args.first().and_then(|a| Path::new(a).file_name())
        .map(|f| f.to_string_lossy().into_owned())
        .unwrap_or_else(|| "?".into())
}

fn find_lean_file(args: &[String]) -> Option<String> {
    for arg in args {
        let path_str = arg.strip_prefix("file://").unwrap_or(arg);
        if path_str.ends_with(".lean") {
            let p = Path::new(path_str);
            // Show path relative to the project root (look for /AKS/ component).
            let display = if let Some(idx) = path_str.rfind("/AKS/") {
                path_str[idx + 1..].to_string()  // "AKS/Graph/Regular.lean"
            } else {
                p.file_name()
                    .map(|f| f.to_string_lossy().into_owned())
                    .unwrap_or_else(|| path_str.to_string())
            };
            return Some(display);
        }
        // Module names like AKS.Graph.Regular
        if arg.contains('.') && !arg.starts_with('-') && !arg.contains('/') {
            let parts: Vec<&str> = arg.split('.').collect();
            if parts.len() >= 2 && parts[0].chars().next().is_some_and(|c| c.is_uppercase()) {
                return Some(arg.clone());
            }
        }
    }
    None
}

// ── Formatting helpers ────────────────────────────────────────────────────────

fn format_age(secs: u64) -> String {
    if secs >= 86400 { format!("{}d{:02}h", secs / 86400, (secs % 86400) / 3600) }
    else if secs >= 3600 { format!("{}h{:02}m", secs / 3600, (secs % 3600) / 60) }
    else if secs >= 60 { format!("{}m{:02}s", secs / 60, secs % 60) }
    else { format!("{}s", secs) }
}

fn format_mem(bytes: u64) -> String {
    if bytes >= 1 << 30 { format!("{:.1}G", bytes as f64 / (1u64 << 30) as f64) }
    else if bytes >= 1 << 20 { format!("{}M", bytes >> 20) }
    else if bytes >= 1 << 10 { format!("{}K", bytes >> 10) }
    else { format!("{}B", bytes) }
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() <= max { s.to_string() }
    else if max > 3 { format!("{}...", &s[..max - 3]) }
    else { s[..max].to_string() }
}

fn format_time() -> String {
    let mut tv: libc::timeval = unsafe { std::mem::zeroed() };
    unsafe { libc::gettimeofday(&mut tv, std::ptr::null_mut()) };
    let mut tm: libc::tm = unsafe { std::mem::zeroed() };
    unsafe { libc::localtime_r(&tv.tv_sec, &mut tm) };
    format!("{:02}:{:02}:{:02}", tm.tm_hour, tm.tm_min, tm.tm_sec)
}

/// Red ← memory pressure; blue ← CPU pressure.
fn row_color(cpu: f64, rss_bytes: u64) -> (u8, u8, u8) {
    let r = ((rss_bytes as f64 / (4.0 * (1u64 << 30) as f64)).min(1.0) * 255.0) as u8;
    let b = ((cpu / 100.0).min(1.0) * 255.0) as u8;
    (r, 0, b)
}

fn frac_color(red_frac: f64, blue_frac: f64) -> (u8, u8, u8) {
    ((red_frac.min(1.0) * 255.0) as u8, 0, (blue_frac.min(1.0) * 255.0) as u8)
}
