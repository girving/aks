//! Compute a PSD certificate for a random d-regular graph.
//!
//! Generates a random d-regular graph on n vertices, computes
//! M = c₁I - c₂B² + c₃J, performs f32 Cholesky factorization in-place,
//! extracts the unit upper-triangular certificate Z via triangular inverse
//! of L, scales to i32, and outputs binary data files.

use faer::linalg::cholesky::llt;
use faer::linalg::cholesky::llt::factor::LltRegularization;
use faer::linalg::triangular_inverse;
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

/// Compute L^{-1} via triangular inverse, then pack Z_unit to i32.
///
/// Uses faer's `invert_lower_triangular` which is O(n³/6) (exploits triangular
/// structure on both input and output), vs O(n³/2) for blocked TRSM.
///
/// Z_unit[i,j] = L^{-T}[i,j] * L[j,j] = L^{-1}[j,i] * L[j,j] for i <= j.
/// Takes ownership of m (Cholesky factor L) to free it after extracting diagonal.
fn compute_and_pack_z(m: Mat<f32>, n: usize, scale: i32) -> (Vec<i32>, f32) {
    use rayon::prelude::*;

    let s = scale as f32;
    let total = n * (n + 1) / 2;

    // Compute L^{-1} (lower triangular) via blocked recursive inverse.
    let par = par_for_n(n);
    let mut l_inv: Mat<f32> = Mat::zeros(n, n);
    triangular_inverse::invert_lower_triangular(l_inv.as_mut(), m.as_ref(), par);

    // Save diagonal of L, then free the Cholesky factor.
    let diag: Vec<f32> = (0..n).map(|j| m[(j, j)]).collect();
    drop(m);

    // Pack: Z_unit[i,j] = L^{-1}[j,i] * L[j,j] for i < j; Z_unit[j,j] = scale.
    // Columns write to disjoint packed regions, so parallelize via raw pointer.
    let mut packed = vec![0i32; total];
    let packed_ptr = packed.as_mut_ptr() as usize; // usize is Send+Sync

    let z_max_offdiag: f32 = (0..n)
        .into_par_iter()
        .map(|j| {
            let col_start = j * (j + 1) / 2;
            let l_jj = diag[j];
            let mut local_max: f32 = 0.0;

            for i in 0..j {
                let z_val = l_inv[(j, i)] * l_jj;
                let abs_z = z_val.abs();
                if abs_z > local_max {
                    local_max = abs_z;
                }
                // SAFETY: Each column j writes to packed[col_start+i] for i < j.
                // Column ranges are non-overlapping.
                unsafe {
                    *(packed_ptr as *mut i32).add(col_start + i) = (z_val * s).round() as i32;
                }
            }
            // Diagonal entry
            unsafe {
                *(packed_ptr as *mut i32).add(col_start + j) = scale;
            }

            local_max
        })
        .reduce(|| 0.0f32, |a, b| a.max(b));

    (packed, z_max_offdiag)
}

/// Post-process Z_int to reduce upper-triangular errors in P = M · Z_int.
/// For each column j, computes P[:,j] exactly via rotation map (i64 arithmetic),
/// then adjusts Z_int[i,j] by integer rounding to minimize |P[i,j]| for i < j.
///
/// Columns are independent (each accesses a disjoint slice of packed), so we
/// split packed into non-overlapping column slices and process in parallel.
fn refine_certificate(
    packed: &mut [i32],
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
    // Column j occupies packed[j*(j+1)/2 .. j*(j+1)/2 + j + 1].
    let mut cols: Vec<&mut [i32]> = Vec::with_capacity(n);
    {
        let mut rest = &mut packed[..];
        for j in 0..n {
            let (col, remaining) = rest.split_at_mut(j + 1);
            cols.push(col);
            rest = remaining;
        }
    }

    cols.into_par_iter().enumerate().for_each_init(
        || {
            (
                vec![0i64; n],                      // z_col
                vec![0i64; n],                      // bz
                vec![0i64; n],                      // p_col
                vec![0i32; n],                      // b2_col
                Vec::<usize>::with_capacity(d * d), // touched
            )
        },
        |(z_col, bz, p_col, b2_col, touched), (j, col)| {
            // Zero z_col (entries from previous column on this thread may be dirty)
            for k in 0..n {
                z_col[k] = 0;
            }
            for k in 0..=j {
                z_col[k] = col[k] as i64;
            }

            // P[:,j] = c₁·z - c₂·B²z + c₃·colsum
            for v in 0..n {
                let mut acc: i64 = 0;
                let base = v * d;
                for p in 0..d {
                    acc += z_col[neighbors[base + p]];
                }
                bz[v] = acc;
            }
            let col_sum: i64 = z_col[..=j].iter().sum();
            for v in 0..n {
                let mut b2z_v: i64 = 0;
                let base = v * d;
                for p in 0..d {
                    b2z_v += bz[neighbors[base + p]];
                }
                p_col[v] = c1 as i64 * z_col[v] - c2 as i64 * b2z_v + c3 as i64 * col_sum;
            }

            // Greedy correction with B² cross-talk tracking.
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
                let d64 = delta as i64;
                col[i] += delta;
                running_delta_sum += d64;

                // Compute B²[v,i] for all v via 2-hop neighbors of i
                touched.clear();
                let base_i = i * d;
                for p in 0..d {
                    let w = neighbors[base_i + p];
                    let base_w = w * d;
                    for q in 0..d {
                        let v = neighbors[base_w + q];
                        if b2_col[v] == 0 {
                            touched.push(v);
                        }
                        b2_col[v] += 1;
                    }
                }

                p_col[i] += (c1 as i64 - c2 as i64 * d as i64) * d64;

                for &v in touched.iter() {
                    if v != i {
                        p_col[v] += -c2 as i64 * b2_col[v] as i64 * d64;
                    }
                    b2_col[v] = 0;
                }
            }
        },
    );
}

/// Verify the certificate using the same logic as the Lean checker.
/// Columns are independent, so we process them in parallel.
fn verify_certificate(
    neighbors: &[usize],
    z_packed: &[i32],
    n: usize,
    d: usize,
    c1: i32,
    c2: i32,
    c3: i32,
) -> (bool, i64, i64, f64) {
    use rayon::prelude::*;

    // map_init allocates scratch buffers once per thread (not per column).
    let (min_diag, eps_max) = (0..n)
        .into_par_iter()
        .map_init(
            || (vec![0i64; n], vec![0i64; n], vec![0i64; n]),
            |(z_col, bz, b2z), j| {
                let col_start = j * (j + 1) / 2;
                for k in 0..n {
                    z_col[k] = 0;
                }
                for k in 0..=j {
                    z_col[k] = z_packed[col_start + k] as i64;
                }

                for v in 0..n {
                    let mut acc: i64 = 0;
                    let base = v * d;
                    for p in 0..d {
                        acc += z_col[neighbors[base + p]];
                    }
                    bz[v] = acc;
                }

                for v in 0..n {
                    let mut acc: i64 = 0;
                    let base = v * d;
                    for p in 0..d {
                        acc += bz[neighbors[base + p]];
                    }
                    b2z[v] = acc;
                }

                let col_sum: i64 = z_col[..=j].iter().sum();

                let mut col_min_diag: i64 = i64::MAX;
                let mut col_eps_max: i64 = 0;

                // Only compute p_ij for i <= j (skip lower-triangular)
                for i in 0..j {
                    let p_ij =
                        c1 as i64 * z_col[i] - c2 as i64 * b2z[i] + c3 as i64 * col_sum;
                    let abs_p = p_ij.abs();
                    if abs_p > col_eps_max {
                        col_eps_max = abs_p;
                    }
                }
                // Diagonal
                let p_jj = c1 as i64 * z_col[j] - c2 as i64 * b2z[j] + c3 as i64 * col_sum;
                col_min_diag = col_min_diag.min(p_jj);

                (col_min_diag, col_eps_max)
            },
        )
        .reduce(
            || (i64::MAX, 0i64),
            |(md1, em1), (md2, em2)| (md1.min(md2), em1.max(em2)),
        );

    let threshold = eps_max
        .checked_mul((n * (n + 1) / 2) as i64)
        .expect("threshold overflow");
    let passes = min_diag > threshold;
    let margin = if threshold > 0 {
        min_diag as f64 / threshold as f64
    } else {
        f64::INFINITY
    };

    (passes, min_diag, eps_max, margin)
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

    // Blocked TRSM + pack: compute Z_unit columns in blocks and pack to i32.
    // Only allocates n × block_size f32 scratch (~20 MB), not a full n×n matrix.
    eprintln!(
        "Triangular inverse + pack ({} packed i32)...",
        fmt_bytes(n as u64 * (n as u64 + 1) / 2 * 4)
    );
    let t0 = Instant::now();
    let (mut z_packed, z_max) = compute_and_pack_z(m, n, scale);
    let trsm_time = t0.elapsed();
    eprintln!("  Z max off-diagonal: {z_max:.6}");
    eprintln!(
        "  Max |Z_int| ≈ {:.0}, i32 limit: {}",
        z_max * scale as f32,
        i32::MAX
    );
    assert!(
        (z_max * scale as f32) < i32::MAX as f32,
        "Z entries overflow i32! Reduce scale_exp."
    );
    eprintln!(
        "  Packed: {} entries [{}]",
        z_packed.len(),
        fmt_duration(trsm_time)
    );

    // Post-process: greedy Gershgorin correction (two passes for c₃ cross-talk convergence)
    let t0 = Instant::now();
    eprintln!("Refining certificate (pass 1)...");
    refine_certificate(&mut z_packed, &neighbors, n, d, c1, c2, c3);
    eprintln!("Refining certificate (pass 2)...");
    refine_certificate(&mut z_packed, &neighbors, n, d, c1, c2, c3);
    eprintln!("  Refinement done [{}]", fmt_duration(t0.elapsed()));

    // Verify
    eprintln!("Verifying certificate...");
    let t0 = Instant::now();
    let (passes, min_diag, eps_max, margin) =
        verify_certificate(&neighbors, &z_packed, n, d, c1, c2, c3);
    eprintln!("  min P[j,j]: {min_diag}");
    eprintln!("  max |P[i,j]| upper-tri: {eps_max}");
    eprintln!(
        "  threshold: {}",
        eps_max as i128 * ((n * (n + 1) / 2) as i128)
    );
    eprintln!("  Gershgorin margin: {margin:.1}x");
    eprintln!(
        "  Certificate passes: {passes} [{}]",
        fmt_duration(t0.elapsed())
    );

    if !passes {
        eprintln!("ERROR: Certificate verification failed!");
        std::process::exit(1);
    }

    // Write binary data files (bulk I/O)
    fs::create_dir_all(&output_dir).expect("Cannot create output dir");

    let rot_path = output_dir.join("rot_map.bin");
    eprintln!("Writing rotation map to {}...", rot_path.display());
    write_i32_bulk(&rot_path, &rot);
    eprintln!(
        "  {} ({} entries)",
        fmt_bytes(rot.len() as u64 * 4),
        rot.len()
    );

    let cert_path = output_dir.join("cert_z.bin");
    eprintln!("Writing certificate to {}...", cert_path.display());
    write_i32_bulk(&cert_path, &z_packed);
    eprintln!(
        "  {} ({} entries)",
        fmt_bytes(z_packed.len() as u64 * 4),
        z_packed.len()
    );

    // Summary
    eprintln!("---");
    eprintln!("Total time: {}", fmt_duration(t_total.elapsed()));
    if let Some(rss) = peak_rss_bytes() {
        eprintln!("Peak RSS: {}", fmt_bytes(rss));
    }
    eprintln!("Done! Generated {}", output_dir.display());
}
