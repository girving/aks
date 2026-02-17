#!/usr/bin/env -S cargo +nightly -Zscript
---cargo
[dependencies]
bytemuck = { version = "1", features = ["derive"] }
faer = "0.24.0"
rand = "0.8"
rand_chacha = "0.3"
rayon = "1"

[profile.release]
opt-level = 3
---

//! Compute a PSD certificate for a random d-regular graph.
//!
//! Generates a random d-regular graph on n vertices, computes
//! M = c₁I - c₂B² + c₃J, performs f32 Cholesky factorization in-place,
//! then streams the certificate: for each block of columns, solves L^T·X = I
//! to get rows of L⁻¹, packs/refines/verifies/writes to disk, and discards.
//! Peak memory: M + one TRSM block ≈ 1.74 GB at n=20736 (no full L⁻¹ or
//! z_packed allocation).

use faer::linalg::cholesky::llt;
use faer::linalg::cholesky::llt::factor::LltRegularization;
use faer::linalg::triangular_solve;
use faer::prelude::*;
use rand::prelude::*;
use rand_chacha::ChaCha20Rng;
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

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

/// Choose parallelism level based on matrix size.
/// Par::rayon(0) has ~90ms overhead at n=1728 but massive wins at n=20736+.
fn par_for_n(n: usize) -> Par {
    if n >= 4000 {
        Par::rayon(0)
    } else {
        Par::Seq
    }
}

/// Build a flat neighbor array from the rotation map.
/// Returns Vec<usize> of size n*d where neighbors[v*d + p] = neighbor of v at port p.
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

/// Generate a random d-regular simple graph on n vertices.
///
/// Uses the configuration model to get a d-regular multigraph, then
/// edge-switching to remove self-loops and multi-edges.
fn make_regular_graph(n: usize, d: usize, rng: &mut impl Rng) -> Vec<Vec<usize>> {
    assert!(n * d % 2 == 0, "n*d must be even");
    assert!(d < n, "d must be less than n for a simple graph");

    let num_edges = n * d / 2;

    // Configuration model: pair stubs randomly
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

    // Edge switching: fix self-loops and multi-edges
    // Pre-allocate seen sets to avoid repeated allocation
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
        assert_eq!(
            adj[v].len(),
            d,
            "Vertex {} has degree {} != {}",
            v,
            adj[v].len(),
            d
        );
    }

    adj
}

/// Find the index of a bad edge (self-loop or multi-edge), or None if all are valid.
/// Takes pre-allocated seen sets; clears them before use.
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

/// Build rotation map from adjacency lists.
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

/// Verify rotation map is a valid involution.
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

/// Compute the J coefficient c₃ such that M = c₁I - c₂B² + c₃J is PSD.
fn compute_j_coeff(c1: i32, c2: i32, d: usize, n: usize) -> i32 {
    let deficit = c2 * (d * d) as i32 - c1;
    if deficit < 0 {
        1
    } else {
        deficit / n as i32 + 2
    }
}

/// Compute M = c₁I - c₂B² + c₃J in-place into a faer Mat<f32>.
fn compute_m_inplace(
    neighbors: &[usize],
    n: usize,
    d: usize,
    c1: i32,
    c2: i32,
    c3: i32,
) -> Mat<f32> {
    let mut m: Mat<f32> = Mat::zeros(n, n);
    let mut b2_row = vec![0i32; n];
    for v in 0..n {
        for x in b2_row.iter_mut() {
            *x = 0;
        }
        for p in 0..d {
            let u = neighbors[v * d + p];
            for q in 0..d {
                let w = neighbors[u * d + q];
                b2_row[w] += 1;
            }
        }
        for w in 0..n {
            let diag = if v == w { c1 as f32 } else { 0.0 };
            m[(v, w)] = diag - (c2 as f32) * (b2_row[w] as f32) + c3 as f32;
        }
    }
    m
}

/// Pack TRSM solution into i32 z_packed format for columns [col_start..col_end).
///
/// After solving L^T · X = I_block, column k of `sol` contains row (col_start+k)
/// of L⁻¹. That is, sol[(i, k)] = L⁻¹[col_start+k, i].
///
/// Z_unit column j has entries: Z[i,j] = L⁻¹[j,i] * L[j,j] for i < j, Z[j,j] = scale.
/// Returns (packed_block, max_offdiag) where packed_block contains the contiguous
/// packed data for columns [col_start..col_end).
fn pack_block(
    sol: &Mat<f32>,
    diag: &[f32],
    col_start: usize,
    col_end: usize,
    scale: i32,
) -> (Vec<i32>, f32) {
    use rayon::prelude::*;

    let s = scale as f32;
    let block_packed_len = col_end * (col_end + 1) / 2 - col_start * (col_start + 1) / 2;
    let block_offset = col_start * (col_start + 1) / 2;

    let mut packed = vec![0i32; block_packed_len];
    let packed_ptr = packed.as_mut_ptr() as usize; // usize is Send+Sync

    let b_cols = col_end - col_start;
    let block_max: f32 = (0..b_cols)
        .into_par_iter()
        .map(|k| {
            let j = col_start + k;
            let col_off = j * (j + 1) / 2 - block_offset;
            let l_jj = diag[j];
            let mut local_max: f32 = 0.0;

            for i in 0..j {
                // sol[(i, k)] = L⁻¹[j, i]
                let z_val = sol[(i, k)] * l_jj;
                let abs_z = z_val.abs();
                if abs_z > local_max {
                    local_max = abs_z;
                }
                // SAFETY: Each column j writes to packed[col_off + i].
                // Different columns have different j, so col_off ranges are disjoint.
                unsafe {
                    *(packed_ptr as *mut i32).add(col_off + i) = (z_val * s).round() as i32;
                }
            }
            // Diagonal entry
            unsafe {
                *(packed_ptr as *mut i32).add(col_off + j) = scale;
            }

            local_max
        })
        .reduce(|| 0.0f32, |a, b| a.max(b));

    (packed, block_max)
}

/// Post-process Z_int columns [col_start..col_end) to reduce upper-triangular
/// errors in P = M · Z_int. Columns are independent, processed in parallel.
///
/// `packed` contains the contiguous packed data for these columns only.
fn refine_columns(
    packed: &mut [i32],
    col_start: usize,
    col_end: usize,
    neighbors: &[usize],
    n: usize,
    d: usize,
    c1: i32,
    c2: i32,
    c3: i32,
) {
    use rayon::prelude::*;

    let m_diag = c1 as i64 - c2 as i64 * d as i64 + c3 as i64;

    // Split packed into non-overlapping column slices.
    // Column j (absolute index) has j+1 entries.
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
        || {
            (
                vec![0i64; n], // bz
                vec![0i64; n], // p_col
            )
        },
        |(bz, p_col), (idx, col)| {
            let j = col_start + idx;

            bz[..n].fill(0);
            for k in 0..=j {
                let val = col[k] as i64;
                let base = k * d;
                for p in 0..d {
                    bz[neighbors[base + p]] += val;
                }
            }

            let col_sum: i64 = col.iter().map(|&x| x as i64).sum();
            for v in 0..j {
                let mut b2z_v: i64 = 0;
                let base = v * d;
                for p in 0..d {
                    b2z_v += bz[neighbors[base + p]];
                }
                p_col[v] =
                    c1 as i64 * col[v] as i64 - c2 as i64 * b2z_v + c3 as i64 * col_sum;
            }

            let mut running_delta_sum: i64 = 0;
            for i in 0..j {
                let effective_p = p_col[i] + c3 as i64 * running_delta_sum;
                if effective_p == 0 {
                    continue;
                }
                let delta = -((effective_p as f64 / m_diag as f64).round() as i32);
                if delta == 0 {
                    continue;
                }
                col[i] += delta;
                running_delta_sum += delta as i64;
            }
        },
    );
}

/// Verify columns [col_start..col_end) of the certificate.
/// Returns (min_diag, max_eps) for these columns.
///
/// `packed` contains the contiguous packed data for these columns only.
fn verify_columns(
    packed: &[i32],
    col_start: usize,
    col_end: usize,
    neighbors: &[usize],
    n: usize,
    d: usize,
    c1: i32,
    c2: i32,
    c3: i32,
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
                    for p in 0..d {
                        bz[neighbors[base + p]] += val;
                    }
                }

                for v in 0..=j {
                    let mut acc: i64 = 0;
                    let base = v * d;
                    for p in 0..d {
                        acc += bz[neighbors[base + p]];
                    }
                    b2z[v] = acc;
                }

                let col_sum: i64 = z_col.iter().map(|&x| x as i64).sum();

                let mut col_min_diag: i64 = i64::MAX;
                let mut col_eps_max: i64 = 0;

                for i in 0..j {
                    let p_ij = c1 as i64 * z_col[i] as i64 - c2 as i64 * b2z[i]
                        + c3 as i64 * col_sum;
                    let abs_p = p_ij.abs();
                    if abs_p > col_eps_max {
                        col_eps_max = abs_p;
                    }
                }
                // Diagonal
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

/// Write a slice of i32 values as little-endian bytes in a single bulk write.
fn write_i32_bulk(path: &std::path::Path, data: &[i32]) {
    let bytes: &[u8] = bytemuck::cast_slice(data);
    fs::write(path, bytes).unwrap_or_else(|e| panic!("Cannot write {}: {}", path.display(), e));
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(16);
    let d: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(4);
    let seed: u64 = args
        .get(3)
        .and_then(|s| s.parse().ok())
        .unwrap_or(42);
    let scale_exp: u32 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(30);
    let output_dir: PathBuf = args
        .get(5)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(&format!("data/{n}")));

    let scale: i32 = 1i32 << scale_exp;

    // M = c₁I - c₂B² + c₃J. Spectral gap bound: β = √(c₁/c₂)/d.
    // Default: c₁ = 8·c₂·(d-1). For d=12: c₁=792, β≈0.782.
    let c2: i32 = 9;
    let c1: i32 = args
        .get(6)
        .and_then(|s| s.parse().ok())
        .unwrap_or(8 * c2 * (d as i32 - 1));
    let beta_num = (c1 as f64 / c2 as f64).sqrt();
    let beta = beta_num / d as f64;
    let c3 = compute_j_coeff(c1, c2, d, n);

    eprintln!("Parameters: n={n}, d={d}, seed={seed}, scale=2^{scale_exp}");
    eprintln!("M = {c1}I - {c2}B² + {c3}J");
    eprintln!("Spectral gap bound: β = √({c1}/{c2})/{d} = {beta:.6}");
    eprintln!(
        "  (β·d = {:.6}, Alon-Boppana: 2√(d-1) = {:.6})",
        beta_num,
        2.0 * ((d as f64) - 1.0).sqrt()
    );

    let t_total = Instant::now();

    // Generate random regular graph
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    eprintln!("Generating {d}-regular graph on {n} vertices...");
    let t0 = Instant::now();
    let adj = make_regular_graph(n, d, &mut rng);

    // Build rotation map (i32)
    let rot = build_rotation_map(&adj, n, d);
    drop(adj);
    assert!(
        verify_involution(&rot, n, d),
        "Rotation map is not a valid involution!"
    );
    eprintln!(
        "  Rotation map: {} entries, involution verified [{}]",
        rot.len(),
        fmt_duration(t0.elapsed())
    );

    // Build flat neighbor array (shared across all phases)
    let neighbors = build_neighbors(&rot, n, d);

    // Compute M = c₁I - c₂B² + c₃J (single n×n f32 allocation)
    eprintln!("Computing M ({} f32)...", fmt_bytes(n as u64 * n as u64 * 4));
    let t0 = Instant::now();
    let mut m = compute_m_inplace(&neighbors, n, d, c1, c2, c3);
    eprintln!("  M[0,0] = {} [{}]", m[(0, 0)], fmt_duration(t0.elapsed()));

    // Cholesky factorization in-place (f32)
    eprintln!("Cholesky factorization (f32, in-place)...");
    let t0 = Instant::now();
    {
        use faer::dyn_stack::{MemBuffer, MemStack};
        let par = par_for_n(n);
        let params = Default::default();
        let scratch_req = llt::factor::cholesky_in_place_scratch::<f32>(n, par, params);
        let mut buf = MemBuffer::new(scratch_req);
        let stack = &mut MemStack::new(&mut buf);
        llt::factor::cholesky_in_place(
            m.as_mut(),
            LltRegularization::default(),
            par,
            stack,
            params,
        )
        .expect("M is not positive definite!");
    }
    eprintln!(
        "  L[0,0] = {:.6} [{}]",
        m[(0, 0)],
        fmt_duration(t0.elapsed())
    );

    // Streaming pipeline: for each block of z_packed columns, solve L^T · X = I,
    // pack to i32, refine (2 passes), verify, and write to cert_z.bin.
    // z_packed is never fully resident — only one block at a time.
    // Peak memory: M + TRSM block ≈ 1.74 GB at n=20736.
    let total = n * (n + 1) / 2;
    let diag: Vec<f32> = (0..n).map(|j| m[(j, j)]).collect();
    let par = par_for_n(n);

    eprintln!(
        "Streaming TRSM + refine + verify ({} packed i32)...",
        fmt_bytes(total as u64 * 4)
    );
    let t0 = Instant::now();

    fs::create_dir_all(&output_dir).expect("Cannot create output dir");
    let cert_path = output_dir.join("cert_z.bin");
    let cert_file = fs::File::create(&cert_path)
        .unwrap_or_else(|e| panic!("Cannot create {}: {}", cert_path.display(), e));
    let mut cert_writer = std::io::BufWriter::new(cert_file);

    const BLOCK: usize = 256;
    let mut z_max_offdiag: f32 = 0.0;
    let mut global_min_diag: i64 = i64::MAX;
    let mut global_eps_max: i64 = 0;
    let mut total_entries: usize = 0;

    for b_start in (0..n).step_by(BLOCK) {
        let b_end = (b_start + BLOCK).min(n);
        let b_cols = b_end - b_start;

        // Solve L^T · X = I_block. Column k of the solution gives row (b_start+k)
        // of L⁻¹: sol[(i, k)] = L⁻¹[b_start+k, i]. These pack directly into
        // contiguous z_packed columns [b_start..b_end).
        let mut sol: Mat<f32> = Mat::zeros(n, b_cols);
        for k in 0..b_cols {
            sol[(b_start + k, k)] = 1.0;
        }
        triangular_solve::solve_upper_triangular_in_place(
            m.as_ref().transpose(),
            sol.as_mut(),
            par,
        );

        // Pack TRSM results into i32.
        let (mut packed_block, block_max) = pack_block(&sol, &diag, b_start, b_end, scale);
        z_max_offdiag = z_max_offdiag.max(block_max);
        drop(sol);

        assert!(
            (z_max_offdiag * scale as f32) < i32::MAX as f32,
            "Z entries overflow i32! Reduce scale_exp."
        );

        // Refine (2 passes) and verify this block.
        refine_columns(&mut packed_block, b_start, b_end, &neighbors, n, d, c1, c2, c3);
        refine_columns(&mut packed_block, b_start, b_end, &neighbors, n, d, c1, c2, c3);

        let (block_min, block_eps) =
            verify_columns(&packed_block, b_start, b_end, &neighbors, n, d, c1, c2, c3);
        global_min_diag = global_min_diag.min(block_min);
        global_eps_max = global_eps_max.max(block_eps);

        // Write block to cert_z.bin (blocks are contiguous and sequential).
        {
            use std::io::Write;
            let bytes: &[u8] = bytemuck::cast_slice(&packed_block);
            cert_writer
                .write_all(bytes)
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
    eprintln!(
        "  Max |Z_int| ≈ {:.0}, i32 limit: {}",
        z_max_offdiag * scale as f32,
        i32::MAX
    );
    eprintln!("  min P[j,j]: {global_min_diag}");
    eprintln!("  max |P[i,j]| upper-tri: {global_eps_max}");

    let threshold = global_eps_max
        .checked_mul(total as i64)
        .expect("threshold overflow");
    let passes = global_min_diag > threshold;
    let margin = if threshold > 0 {
        global_min_diag as f64 / threshold as f64
    } else {
        f64::INFINITY
    };

    eprintln!(
        "  threshold: {}",
        global_eps_max as i128 * (total as i128)
    );
    eprintln!("  Gershgorin margin: {margin:.1}x");
    eprintln!(
        "  Streamed: {} entries, passes={passes} [{}]",
        total_entries,
        fmt_duration(stream_time)
    );

    if !passes {
        eprintln!("ERROR: Certificate verification failed!");
        std::process::exit(1);
    }

    // Write rotation map
    let rot_path = output_dir.join("rot_map.bin");
    eprintln!("Writing rotation map to {}...", rot_path.display());
    write_i32_bulk(&rot_path, &rot);
    eprintln!(
        "  {} ({} entries)",
        fmt_bytes(rot.len() as u64 * 4),
        rot.len()
    );
    eprintln!(
        "  cert_z.bin: {} ({} entries)",
        fmt_bytes(total_entries as u64 * 4),
        total_entries
    );

    // Summary
    eprintln!("---");
    eprintln!("Total time: {}", fmt_duration(t_total.elapsed()));
    if let Some(rss) = peak_rss_bytes() {
        eprintln!("Peak RSS: {}", fmt_bytes(rss));
    }
    eprintln!("Done! Generated {}", output_dir.display());
}
