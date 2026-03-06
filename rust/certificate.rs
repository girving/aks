#!/usr/bin/env -S cargo +nightly -Zscript
---cargo
[dependencies]
bytemuck = { version = "1", features = ["derive"] }
faer = "0.24.0"
faer-traits = "0.24.0"
rand = "0.8"
rand_chacha = "0.3"
rayon = "1"

# cargo-script defaults to the dev profile, so override it for speed.
# Without this, faer's SIMD kernels are unoptimized and Cholesky is ~200x slower.
[profile.dev]
opt-level = 3
overflow-checks = false
debug = false

[profile.release]
opt-level = 3
---

//! Compute a PSD certificate for a random d-regular graph.
//!
//! Usage: certificate.rs -n=N -d=D [options]
//!
//! Required:
//!   -n=N          Number of vertices
//!   -d=D          Degree of regular graph
//!
//! Optional:
//!   --seed=S      RNG seed (default: 42)
//!   --scale=S     Integer scale factor for Z entries (default: 1073741824 = 2^30)
//!   --out=DIR     Output directory (default: data/N)
//!   --c1=C        Override c₁ in M = c₁I - c₂B² + c₃J (default: 8·9·(d-1))
//!   --c2=C        Override c₂ (default: 9)
//!   --refine=R    Number of refinement passes (default: 2)
//!   --f64         Use f64 precision for Cholesky/TRSM (default: f32)
//!   --format=FMT  Output format: b85 (default) or b128 (3-byte base-128, off-diag only)

use faer::linalg::cholesky::llt;
use faer::linalg::cholesky::llt::factor::LltRegularization;
use faer::linalg::triangular_solve;
use faer::prelude::*;
use rand::prelude::*;
use rand_chacha::ChaCha20Rng;
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use faer_traits::ComplexField;

/// Read peak RSS from /proc/self/status (Linux only). Returns bytes.
fn peak_rss_bytes() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    for line in status.lines() {
        if line.starts_with("VmHWM:") {
            let kb_str = line.split_whitespace().nth(1)?;
            let kb: u64 = kb_str.parse().ok()?;
            return Some(kb * 1024);
        }
    }
    None
}

fn fmt_duration(d: std::time::Duration) -> String {
    let s = d.as_secs_f64();
    if s < 1.0 {
        format!("{:.0}ms", s * 1000.0)
    } else if s < 60.0 {
        format!("{:.1}s", s)
    } else {
        format!("{}m{:.0}s", (s / 60.0) as u64, s % 60.0)
    }
}

fn fmt_bytes(b: u64) -> String {
    if b < 1024 * 1024 {
        format!("{:.0} KB", b as f64 / 1024.0)
    } else if b < 1024 * 1024 * 1024 {
        format!("{:.1} MB", b as f64 / (1024.0 * 1024.0))
    } else {
        format!("{:.2} GB", b as f64 / (1024.0 * 1024.0 * 1024.0))
    }
}

fn par_for_n(n: usize) -> Par {
    if n >= 4000 { Par::rayon(0) } else { Par::Seq }
}

fn build_neighbors(rot: &[i32], n: usize, d: usize) -> Vec<usize> {
    let mut neighbors = vec![0usize; n * d];
    for v in 0..n {
        for p in 0..d {
            let k = v * d + p;
            neighbors[k] = rot[2 * k] as usize;
        }
    }
    neighbors
}

fn make_regular_graph(n: usize, d: usize, rng: &mut impl Rng) -> Vec<Vec<usize>> {
    assert!(n * d % 2 == 0, "n*d must be even");
    assert!(d < n, "d must be less than n for a simple graph");

    let num_edges = n * d / 2;
    let mut stubs: Vec<usize> = Vec::with_capacity(n * d);
    for v in 0..n {
        for _ in 0..d {
            stubs.push(v);
        }
    }
    stubs.shuffle(rng);

    let mut edges: Vec<(usize, usize)> = Vec::with_capacity(num_edges);
    for i in (0..stubs.len()).step_by(2) {
        edges.push((stubs[i], stubs[i + 1]));
    }

    let mut seen: Vec<std::collections::HashSet<usize>> = (0..n)
        .map(|_| std::collections::HashSet::with_capacity(d))
        .collect();
    let max_iterations = num_edges * 100;
    for _ in 0..max_iterations {
        let bad = find_bad_edge(&edges, &mut seen);
        let bad_idx = match bad {
            Some(idx) => idx,
            None => break,
        };
        let other_idx = rng.gen_range(0..num_edges);
        if other_idx == bad_idx {
            continue;
        }
        let (a, b) = edges[bad_idx];
        let (c, dd) = edges[other_idx];
        if rng.gen_bool(0.5) {
            edges[bad_idx] = (a, c);
            edges[other_idx] = (b, dd);
        } else {
            edges[bad_idx] = (a, dd);
            edges[other_idx] = (b, c);
        }
    }

    assert!(
        find_bad_edge(&edges, &mut seen).is_none(),
        "Edge switching failed to produce a simple graph"
    );

    let mut adj: Vec<Vec<usize>> = vec![vec![]; n];
    for &(u, v) in &edges {
        adj[u].push(v);
        adj[v].push(u);
    }
    for v in 0..n {
        assert_eq!(adj[v].len(), d, "Vertex {} has degree {} != {}", v, adj[v].len(), d);
    }
    adj
}

fn find_bad_edge(
    edges: &[(usize, usize)],
    seen: &mut [std::collections::HashSet<usize>],
) -> Option<usize> {
    for s in seen.iter_mut() {
        s.clear();
    }
    for (i, &(u, v)) in edges.iter().enumerate() {
        if u == v {
            return Some(i);
        }
        if seen[u].contains(&v) {
            return Some(i);
        }
        seen[u].insert(v);
        seen[v].insert(u);
    }
    None
}

fn build_rotation_map(adj: &[Vec<usize>], n: usize, d: usize) -> Vec<i32> {
    let mut rot = vec![0i32; n * d * 2];
    for v in 0..n {
        for i in 0..d {
            let w = adj[v][i];
            let j = adj[w].iter().position(|&u| u == v).unwrap();
            let k = v * d + i;
            rot[2 * k] = w as i32;
            rot[2 * k + 1] = j as i32;
        }
    }
    rot
}

fn verify_involution(rot: &[i32], n: usize, d: usize) -> bool {
    for k in 0..(n * d) {
        let w = rot[2 * k] as usize;
        let q = rot[2 * k + 1] as usize;
        if w >= n || q >= d {
            return false;
        }
        let k2 = w * d + q;
        let v2 = rot[2 * k2] as usize;
        let p2 = rot[2 * k2 + 1] as usize;
        if v2 * d + p2 != k {
            return false;
        }
    }
    true
}

fn compute_j_coeff(c1: i32, c2: i32, d: usize, n: usize) -> i32 {
    let deficit = c2 * (d * d) as i32 - c1;
    if deficit < 0 { 1 } else { deficit / n as i32 + 2 }
}

/// Trait for float types usable in the certificate pipeline.
/// Both f32 and f64 satisfy these via faer's ComplexField.
trait CertFloat: ComplexField<Real = Self> + faer_traits::RealField + Copy + Send + Sync + std::fmt::Display + 'static {
    fn from_i32(v: i32) -> Self;
    fn to_f64(self) -> f64;
    fn name() -> &'static str;
    fn bytes_per_element() -> u64;
}

impl CertFloat for f32 {
    #[inline] fn from_i32(v: i32) -> Self { v as f32 }
    #[inline] fn to_f64(self) -> f64 { self as f64 }
    fn name() -> &'static str { "f32" }
    fn bytes_per_element() -> u64 { 4 }
}

impl CertFloat for f64 {
    #[inline] fn from_i32(v: i32) -> Self { v as f64 }
    #[inline] fn to_f64(self) -> f64 { self }
    fn name() -> &'static str { "f64" }
    fn bytes_per_element() -> u64 { 8 }
}

/// Compute M = c₁I - c₂B² + c₃J into a faer Mat<F>.
fn compute_m<F: CertFloat>(
    neighbors: &[usize], n: usize, d: usize, c1: i32, c2: i32, c3: i32,
) -> Mat<F> {
    let mut m: Mat<F> = Mat::zeros(n, n);
    let mut b2_row = vec![0i32; n];
    for v in 0..n {
        b2_row.fill(0);
        for p in 0..d {
            let u = neighbors[v * d + p];
            for q in 0..d {
                b2_row[neighbors[u * d + q]] += 1;
            }
        }
        for w in 0..n {
            let diag = if v == w { F::from_i32(c1) } else { F::from_i32(0) };
            m[(v, w)] = diag - F::from_i32(c2) * F::from_i32(b2_row[w]) + F::from_i32(c3);
        }
    }
    m
}

/// Pack TRSM solution into i32 z_packed for columns [col_start..col_end).
fn pack_block<F: CertFloat>(
    sol: &Mat<F>, diag: &[F], col_start: usize, col_end: usize, scale: i32,
) -> (Vec<i32>, f64) {
    use rayon::prelude::*;

    let block_packed_len = col_end * (col_end + 1) / 2 - col_start * (col_start + 1) / 2;
    let block_offset = col_start * (col_start + 1) / 2;
    let mut packed = vec![0i32; block_packed_len];
    let packed_ptr = packed.as_mut_ptr() as usize;
    let b_cols = col_end - col_start;

    let block_max: f64 = (0..b_cols)
        .into_par_iter()
        .map(|k| {
            let j = col_start + k;
            let col_off = j * (j + 1) / 2 - block_offset;
            let l_jj = diag[j].to_f64();
            let s = scale as f64;
            let mut local_max: f64 = 0.0;
            for i in 0..j {
                let z_val = sol[(i, k)].to_f64() * l_jj;
                let abs_z = z_val.abs();
                if abs_z > local_max { local_max = abs_z; }
                unsafe {
                    *(packed_ptr as *mut i32).add(col_off + i) = (z_val * s).round() as i32;
                }
            }
            unsafe {
                *(packed_ptr as *mut i32).add(col_off + j) = scale;
            }
            local_max
        })
        .reduce(|| 0.0f64, |a, b| a.max(b));

    (packed, block_max)
}

fn refine_columns(
    packed: &mut [i32], col_start: usize, col_end: usize,
    neighbors: &[usize], n: usize, d: usize, c1: i32, c2: i32, c3: i32,
) {
    use rayon::prelude::*;

    let m_diag = c1 as i64 - c2 as i64 * d as i64 + c3 as i64;
    let mut cols: Vec<&mut [i32]> = Vec::with_capacity(col_end - col_start);
    {
        let mut rest = &mut packed[..];
        for j in col_start..col_end {
            let (col, remaining) = rest.split_at_mut(j + 1);
            cols.push(col);
            rest = remaining;
        }
    }

    cols.into_par_iter().enumerate().for_each_init(
        || (vec![0i64; n], vec![0i64; n]),
        |(bz, p_col), (idx, col)| {
            let j = col_start + idx;
            bz[..n].fill(0);
            for k in 0..=j {
                let val = col[k] as i64;
                let base = k * d;
                for p in 0..d { bz[neighbors[base + p]] += val; }
            }
            let col_sum: i64 = col.iter().map(|&x| x as i64).sum();
            for v in 0..j {
                let mut b2z_v: i64 = 0;
                let base = v * d;
                for p in 0..d { b2z_v += bz[neighbors[base + p]]; }
                p_col[v] = c1 as i64 * col[v] as i64 - c2 as i64 * b2z_v + c3 as i64 * col_sum;
            }
            let mut running_delta_sum: i64 = 0;
            for i in 0..j {
                let effective_p = p_col[i] + c3 as i64 * running_delta_sum;
                if effective_p == 0 { continue; }
                let delta = -((effective_p as f64 / m_diag as f64).round() as i32);
                if delta == 0 { continue; }
                col[i] += delta;
                running_delta_sum += delta as i64;
            }
        },
    );
}

fn verify_columns(
    packed: &[i32], col_start: usize, col_end: usize,
    neighbors: &[usize], n: usize, d: usize, c1: i32, c2: i32, c3: i32,
) -> (i64, i64) {
    use rayon::prelude::*;

    let block_offset = col_start * (col_start + 1) / 2;
    (col_start..col_end)
        .into_par_iter()
        .map_init(
            || (vec![0i64; n], vec![0i64; n]),
            |(bz, b2z), j| {
                let col_off = j * (j + 1) / 2 - block_offset;
                let z_col = &packed[col_off..col_off + j + 1];
                bz[..n].fill(0);
                for k in 0..=j {
                    let val = z_col[k] as i64;
                    let base = k * d;
                    for p in 0..d { bz[neighbors[base + p]] += val; }
                }
                for v in 0..=j {
                    let mut acc: i64 = 0;
                    let base = v * d;
                    for p in 0..d { acc += bz[neighbors[base + p]]; }
                    b2z[v] = acc;
                }
                let col_sum: i64 = z_col.iter().map(|&x| x as i64).sum();
                let mut col_min_diag: i64 = i64::MAX;
                let mut col_eps_max: i64 = 0;
                for i in 0..j {
                    let p_ij = c1 as i64 * z_col[i] as i64 - c2 as i64 * b2z[i]
                        + c3 as i64 * col_sum;
                    let abs_p = p_ij.abs();
                    if abs_p > col_eps_max { col_eps_max = abs_p; }
                }
                let p_jj = c1 as i64 * z_col[j] as i64 - c2 as i64 * b2z[j]
                    + c3 as i64 * col_sum;
                col_min_diag = col_min_diag.min(p_jj);
                (col_min_diag, col_eps_max)
            },
        )
        .reduce(
            || (i64::MAX, 0i64),
            |(md1, em1), (md2, em2)| (md1.min(md2), em1.max(em2)),
        )
}

fn encode_base85(data: &[i32]) -> Vec<u8> {
    let mut result = Vec::with_capacity(data.len() * 5);
    for &val in data {
        let mut v = val as u32;
        for _ in 0..5 {
            result.push((v % 85 + 33) as u8);
            v /= 85;
        }
    }
    result
}

fn write_base85(path: &std::path::Path, data: &[i32]) {
    let encoded = encode_base85(data);
    fs::write(path, &encoded)
        .unwrap_or_else(|e| panic!("Cannot write {}: {}", path.display(), e));
}

/// Encode off-diagonal entries from a packed block in 3-byte base-128.
/// Diagonals (position i == j) are skipped. Each signed value v is encoded as:
///   u = v + 1048576;  bytes = [u%128, (u/128)%128, u/16384]
/// Range: [-1048576, 1048575]. Panics if any off-diagonal value is out of range.
/// Encode off-diagonal entries from a packed block in 3-byte base-128 with sentinel.
/// Values in [-1048576, 1048575] are encoded directly as 3 bytes (each 0–127).
/// Values outside this range are encoded as the sentinel (0, 0, 0) and appended to `overflow`.
fn encode_compact_offdiag(packed: &[i32], col_start: usize, col_end: usize) -> Vec<u8> {
    let block_offset = col_start * (col_start + 1) / 2;
    let mut result = Vec::new();
    for j in col_start..col_end {
        let col_off = j * (j + 1) / 2 - block_offset;
        for i in 0..j {
            let val = packed[col_off + i];
            let u = (val as i64 + 134217728) as u64;  // 128^4/2 = 134217728
            assert!(u < 268435456,  // 128^4
                "Value {} out of 4-byte base-128 range at ({}, {})", val, i, j);
            result.push((u % 128) as u8);
            result.push(((u / 128) % 128) as u8);
            result.push(((u / 16384) % 128) as u8);
            result.push((u / 2097152) as u8);
        }
    }
    result
}

/// Encode off-diagonal entries from a packed block in 5-byte base-128.
/// Range: [-17179869184, 17179869183] (128^5/2).
fn encode_compact_offdiag_5byte(packed: &[i32], col_start: usize, col_end: usize) -> Vec<u8> {
    let block_offset = col_start * (col_start + 1) / 2;
    let mut result = Vec::new();
    for j in col_start..col_end {
        let col_off = j * (j + 1) / 2 - block_offset;
        for i in 0..j {
            let val = packed[col_off + i];
            let u = (val as i64 + 17179869184) as u64;  // 128^5/2
            assert!(u < 34359738368,  // 128^5
                "Value {} out of 5-byte base-128 range at ({}, {})", val, i, j);
            result.push((u % 128) as u8);
            result.push(((u / 128) % 128) as u8);
            result.push(((u / 16384) % 128) as u8);
            result.push(((u / 2097152) % 128) as u8);
            result.push((u / 268435456) as u8);
        }
    }
    result
}

/// Encode rotation map in compact 4-byte format: 3 b85 bytes for vertex + 1 b85 byte for port.
/// Requires n < 85³ = 614125 and d < 85.
fn write_compact_rot(path: &std::path::Path, rot: &[i32], n: usize, d: usize) {
    assert!(n < 614125, "n={n} too large for 3-byte b85 vertex encoding (max 614125)");
    assert!(d < 85, "d={d} too large for 1-byte b85 port encoding (max 85)");
    let nd = n * d;
    let mut result = Vec::with_capacity(nd * 4);
    for k in 0..nd {
        let v = rot[2 * k] as u32;
        let p = rot[2 * k + 1] as u32;
        result.push((v % 85 + 33) as u8);
        result.push((v / 85 % 85 + 33) as u8);
        result.push((v / 7225 + 33) as u8); // 7225 = 85²
        result.push((p + 33) as u8);
    }
    fs::write(path, &result)
        .unwrap_or_else(|e| panic!("Cannot write {}: {}", path.display(), e));
}

/// Run the full certificate pipeline with float type F (f32 or f64).
fn run_pipeline<F: CertFloat>(cfg: &Config) {
    let n = cfg.n;
    let d = cfg.d;
    let scale = cfg.scale;

    let c3 = compute_j_coeff(cfg.c1, cfg.c2, d, n);
    let beta_num = (cfg.c1 as f64 / cfg.c2 as f64).sqrt();
    let beta = beta_num / d as f64;
    let elem_bytes = F::bytes_per_element();

    eprintln!("Parameters: n={n}, d={d}, seed={}, scale={}, precision={}",
        cfg.seed, scale, F::name());
    eprintln!("Refinement passes: {}", cfg.refine);
    eprintln!("M = {}I - {}B² + {c3}J", cfg.c1, cfg.c2);
    eprintln!("Spectral gap bound: β = √({}/{})/{d} = {beta:.6}", cfg.c1, cfg.c2);
    eprintln!("  (β·d = {beta_num:.6}, Alon-Boppana: 2√(d-1) = {:.6})",
        2.0 * ((d as f64) - 1.0).sqrt());

    let t_total = Instant::now();

    // Generate random regular graph
    let mut rng = ChaCha20Rng::seed_from_u64(cfg.seed);
    eprintln!("Generating {d}-regular graph on {n} vertices...");
    let t0 = Instant::now();
    let adj = make_regular_graph(n, d, &mut rng);
    let rot = build_rotation_map(&adj, n, d);
    drop(adj);
    assert!(verify_involution(&rot, n, d), "Rotation map is not a valid involution!");
    eprintln!("  Rotation map: {} entries, involution verified [{}]",
        rot.len(), fmt_duration(t0.elapsed()));

    let neighbors = build_neighbors(&rot, n, d);

    // Compute M
    let m_bytes = n as u64 * n as u64 * elem_bytes;
    eprintln!("Computing M ({} {})...", fmt_bytes(m_bytes), F::name());
    let t0 = Instant::now();
    let mut m = compute_m::<F>(&neighbors, n, d, cfg.c1, cfg.c2, c3);
    eprintln!("  M[0,0] = {} [{}]", m[(0, 0)], fmt_duration(t0.elapsed()));

    // Cholesky
    eprintln!("Cholesky factorization ({}, in-place)...", F::name());
    let t0 = Instant::now();
    {
        use faer::dyn_stack::{MemBuffer, MemStack};
        let par = par_for_n(n);
        let params = Default::default();
        let scratch_req = llt::factor::cholesky_in_place_scratch::<F>(n, par, params);
        let mut buf = MemBuffer::new(scratch_req);
        llt::factor::cholesky_in_place(
            m.as_mut(), LltRegularization::default(), par,
            &mut MemStack::new(&mut buf), params,
        ).expect("M is not positive definite!");
    }
    eprintln!("  L[0,0] = {:.6} [{}]", m[(0, 0)].to_f64(), fmt_duration(t0.elapsed()));

    // Streaming TRSM + refine + verify + write
    let total = n * (n + 1) / 2;
    let diag: Vec<F> = (0..n).map(|j| m[(j, j)]).collect();
    let par = par_for_n(n);

    eprintln!("Streaming TRSM + refine + verify ({} packed i32)...",
        fmt_bytes(total as u64 * 4));
    let t0 = Instant::now();

    fs::create_dir_all(&cfg.out).expect("Cannot create output dir");
    let cert_ext = match cfg.format {
        CertFormat::B85 => "b85",
        CertFormat::B128 => "b128",
        CertFormat::B128x5 => "b128x5",
    };
    let cert_path = cfg.out.join(format!("cert_z.{cert_ext}"));
    let cert_file = fs::File::create(&cert_path)
        .unwrap_or_else(|e| panic!("Cannot create {}: {}", cert_path.display(), e));
    let mut cert_writer = std::io::BufWriter::new(cert_file);

    const BLOCK: usize = 2048;
    let mut z_max_offdiag: f64 = 0.0;
    let mut global_min_diag: i64 = i64::MAX;
    let mut global_eps_max: i64 = 0;
    let mut total_entries: usize = 0;

    for b_start in (0..n).step_by(BLOCK) {
        let b_end = (b_start + BLOCK).min(n);
        let b_cols = b_end - b_start;

        let mut sol: Mat<F> = Mat::zeros(n, b_cols);
        for k in 0..b_cols {
            sol[(b_start + k, k)] = F::from_i32(1);
        }
        triangular_solve::solve_upper_triangular_in_place(
            m.as_ref().transpose(), sol.as_mut(), par,
        );

        let (mut packed_block, block_max) = pack_block(&sol, &diag, b_start, b_end, scale);
        z_max_offdiag = z_max_offdiag.max(block_max);
        drop(sol);

        assert!(
            (z_max_offdiag * scale as f64) < i32::MAX as f64,
            "Z entries overflow i32! Reduce --scale."
        );

        for _ in 0..cfg.refine {
            refine_columns(&mut packed_block, b_start, b_end, &neighbors, n, d,
                cfg.c1, cfg.c2, c3);
        }

        let (block_min, block_eps) =
            verify_columns(&packed_block, b_start, b_end, &neighbors, n, d,
                cfg.c1, cfg.c2, c3);
        global_min_diag = global_min_diag.min(block_min);
        global_eps_max = global_eps_max.max(block_eps);

        {
            use std::io::Write;
            let encoded = match cfg.format {
                CertFormat::B85 => encode_base85(&packed_block),
                CertFormat::B128 => encode_compact_offdiag(&packed_block, b_start, b_end),
                CertFormat::B128x5 => encode_compact_offdiag_5byte(&packed_block, b_start, b_end),
            };
            cert_writer.write_all(&encoded)
                .unwrap_or_else(|e| panic!("Write failed: {}", e));
        }
        total_entries += packed_block.len();
    }

    {
        use std::io::Write;
        cert_writer.flush().unwrap();
    }
    drop(cert_writer);
    drop(m);

    let stream_time = t0.elapsed();
    eprintln!("  Z max off-diagonal: {z_max_offdiag:.6}");
    eprintln!("  Max |Z_int| ≈ {:.0}, i32 limit: {}", z_max_offdiag * scale as f64, i32::MAX);
    eprintln!("  min P[j,j]: {global_min_diag}");
    eprintln!("  max |P[i,j]| upper-tri: {global_eps_max}");

    let threshold = global_eps_max as i128 * total as i128;
    let passes = (global_min_diag as i128) > threshold;
    let margin = if threshold > 0 {
        global_min_diag as f64 / threshold as f64
    } else {
        f64::INFINITY
    };

    eprintln!("  threshold: {threshold}");
    eprintln!("  Gershgorin margin: {margin:.1}x");
    eprintln!("  Streamed: {} entries, passes={passes} [{}]",
        total_entries, fmt_duration(stream_time));

    if !passes {
        eprintln!("ERROR: Certificate verification failed!");
        std::process::exit(1);
    }

    // Write rotation map
    let rot_path = cfg.out.join("rot_map.b85");
    eprintln!("Writing rotation map to {}...", rot_path.display());
    write_base85(&rot_path, &rot);
    eprintln!("  {} ({} entries, {} base85)",
        fmt_bytes(rot.len() as u64 * 4), rot.len(), fmt_bytes(rot.len() as u64 * 5));
    let compact_rot_path = cfg.out.join("rot_map.b85c");
    write_compact_rot(&compact_rot_path, &rot, n, d);
    eprintln!("  rot_map.b85c: {} ({} half-edges, 4 bytes each)",
        fmt_bytes((n * d * 4) as u64), n * d);
    match cfg.format {
        CertFormat::B85 => eprintln!("  cert_z.b85: {} ({} entries, {} base85)",
            fmt_bytes(total_entries as u64 * 4), total_entries,
            fmt_bytes(total_entries as u64 * 5)),
        CertFormat::B128 => {
            let compact_entries = n * (n - 1) / 2;
            eprintln!("  cert_z.b128: {} off-diag entries, {}",
                compact_entries, fmt_bytes(compact_entries as u64 * 4));
        }
        CertFormat::B128x5 => {
            let compact_entries = n * (n - 1) / 2;
            eprintln!("  cert_z.b128x5: {} off-diag entries, {}",
                compact_entries, fmt_bytes(compact_entries as u64 * 5));
        }
    }

    eprintln!("---");
    eprintln!("Total time: {}", fmt_duration(t_total.elapsed()));
    if let Some(rss) = peak_rss_bytes() {
        eprintln!("Peak RSS: {}", fmt_bytes(rss));
    }
    eprintln!("Done! Generated {}", cfg.out.display());
}

#[derive(Clone, Copy, PartialEq)]
enum CertFormat { B85, B128, B128x5 }

struct Config {
    n: usize,
    d: usize,
    seed: u64,
    scale: i32,
    out: PathBuf,
    c1: i32,
    c2: i32,
    refine: usize,
    use_f64: bool,
    format: CertFormat,
}

fn parse_flag<T: std::str::FromStr>(args: &[String], name: &str) -> Option<T> {
    let prefix = format!("{}=", name);
    args.iter()
        .find_map(|a| a.strip_prefix(&prefix).and_then(|v| v.parse().ok()))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let n: usize = parse_flag(&args, "-n")
        .expect("Required: -n=N (number of vertices)");
    let d: usize = parse_flag(&args, "-d")
        .expect("Required: -d=D (degree)");
    let seed: u64 = parse_flag(&args, "--seed").unwrap_or(42);
    let scale: i32 = parse_flag(&args, "--scale").unwrap_or(1 << 30);
    assert!(scale > 0, "--scale must be a positive i32 (max 2147483647)");
    let c2: i32 = parse_flag(&args, "--c2").unwrap_or(9);
    let c1: i32 = parse_flag(&args, "--c1").unwrap_or(8 * c2 * (d as i32 - 1));
    let refine: usize = parse_flag(&args, "--refine").unwrap_or(2);
    let use_f64 = args.iter().any(|a| a == "--f64");
    let out: PathBuf = parse_flag::<String>(&args, "--out")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(&format!("data/{n}")));

    let format = match parse_flag::<String>(&args, "--format").as_deref() {
        Some("b128") => CertFormat::B128,
        Some("b128x5") => CertFormat::B128x5,
        Some("b85") | None => CertFormat::B85,
        Some(f) => panic!("Unknown --format={f}, expected b85, b128, or b128x5"),
    };

    let cfg = Config { n, d, seed, scale, out, c1, c2, refine, use_f64, format };

    if cfg.use_f64 {
        run_pipeline::<f64>(&cfg);
    } else {
        run_pipeline::<f32>(&cfg);
    }
}
