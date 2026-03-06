#!/usr/bin/env -S RUSTFLAGS=-L/usr/local/cuda/lib64 cargo +nightly -Zscript
---cargo
[dependencies]
rand = "0.8"
rand_chacha = "0.3"
rayon = "1"

# cargo-script defaults to the dev profile, so override it for speed.
[profile.dev]
opt-level = 3
overflow-checks = false
debug = false

[profile.release]
opt-level = 3
---

//! GPU-accelerated PSD certificate generator for random d-regular graphs.
//!
//! Uses raw CUDA FFI to cuSOLVER (Cholesky) and cuBLAS (TRSM) for the O(n^3)
//! operations. Everything else (graph generation, M formation, refinement,
//! verification, encoding) runs on CPU.
//!
//! Usage: gpu-certificate.rs -n=N -d=D [options]
//!
//! Required:
//!   -n=N          Number of vertices
//!   -d=D          Degree of regular graph
//!
//! Optional:
//!   --seed=S      RNG seed (default: 42)
//!   --scale=S     Integer scale factor for Z entries (default: 2^30)
//!   --out=DIR     Output directory (default: data/N)
//!   --c1=C        Override c₁ in M = c₁I - c₂B² + c₃J (default: 8·9·(d-1))
//!   --c2=C        Override c₂ (default: 9)
//!   --refine=R    Number of refinement passes (default: 2)
//!   --f64         Use f64 precision for Cholesky/TRSM (default: f32)
//!   --block=B     TRSM block size (default: 2048)
//!   --gpu=ID      GPU device ID (default: 0)

use rand::prelude::*;
use rand_chacha::ChaCha20Rng;
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

// ═══════════════════════════════════════════════════════════════════════════
// Section 1: CUDA FFI declarations
// ═══════════════════════════════════════════════════════════════════════════

type CudaError = i32;
type CublasHandle = *mut std::ffi::c_void;
type CusolverDnHandle = *mut std::ffi::c_void;

const CUDA_SUCCESS: CudaError = 0;

// cudaMemcpyKind
const CUDA_MEMCPY_H2D: i32 = 1;
const CUDA_MEMCPY_D2H: i32 = 2;

// cublas enums
const CUBLAS_FILL_MODE_LOWER: i32 = 0;
const CUBLAS_SIDE_LEFT: i32 = 0;
const CUBLAS_OP_T: i32 = 1;
const CUBLAS_DIAG_NON_UNIT: i32 = 0;

#[link(name = "cudart")]
unsafe extern "C" {
    fn cudaMalloc(devPtr: *mut *mut std::ffi::c_void, size: usize) -> CudaError;
    fn cudaFree(devPtr: *mut std::ffi::c_void) -> CudaError;
    fn cudaMemcpy(dst: *mut std::ffi::c_void, src: *const std::ffi::c_void,
                  count: usize, kind: i32) -> CudaError;
    fn cudaDeviceSynchronize() -> CudaError;
    fn cudaMemGetInfo(free: *mut usize, total: *mut usize) -> CudaError;
    fn cudaGetErrorString(error: CudaError) -> *const std::ffi::c_char;
    fn cudaSetDevice(device: i32) -> CudaError;
}

#[link(name = "cublas")]
unsafe extern "C" {
    fn cublasCreate_v2(handle: *mut CublasHandle) -> CudaError;
    fn cublasDestroy_v2(handle: CublasHandle) -> CudaError;
    fn cublasStrsm_v2(
        handle: CublasHandle, side: i32, uplo: i32, trans: i32, diag: i32,
        m: i32, n: i32, alpha: *const f32, A: *const std::ffi::c_void, lda: i32,
        B: *mut std::ffi::c_void, ldb: i32,
    ) -> CudaError;
    fn cublasDtrsm_v2(
        handle: CublasHandle, side: i32, uplo: i32, trans: i32, diag: i32,
        m: i32, n: i32, alpha: *const f64, A: *const std::ffi::c_void, lda: i32,
        B: *mut std::ffi::c_void, ldb: i32,
    ) -> CudaError;
    fn cublasGetVector(
        n: i32, elemSize: i32,
        x: *const std::ffi::c_void, incx: i32,
        y: *mut std::ffi::c_void, incy: i32,
    ) -> CudaError;
}

#[link(name = "cusolver")]
unsafe extern "C" {
    fn cusolverDnCreate(handle: *mut CusolverDnHandle) -> CudaError;
    fn cusolverDnDestroy(handle: CusolverDnHandle) -> CudaError;
    fn cusolverDnSpotrf_bufferSize(
        handle: CusolverDnHandle, uplo: i32, n: i32,
        A: *const std::ffi::c_void, lda: i32, lwork: *mut i32,
    ) -> CudaError;
    fn cusolverDnDpotrf_bufferSize(
        handle: CusolverDnHandle, uplo: i32, n: i32,
        A: *const std::ffi::c_void, lda: i32, lwork: *mut i32,
    ) -> CudaError;
    fn cusolverDnSpotrf(
        handle: CusolverDnHandle, uplo: i32, n: i32,
        A: *mut std::ffi::c_void, lda: i32,
        workspace: *mut std::ffi::c_void, lwork: i32,
        devInfo: *mut i32,
    ) -> CudaError;
    fn cusolverDnDpotrf(
        handle: CusolverDnHandle, uplo: i32, n: i32,
        A: *mut std::ffi::c_void, lda: i32,
        workspace: *mut std::ffi::c_void, lwork: i32,
        devInfo: *mut i32,
    ) -> CudaError;
}

// ═══════════════════════════════════════════════════════════════════════════
// Section 2: CUDA helpers
// ═══════════════════════════════════════════════════════════════════════════

fn cuda_error_string(err: CudaError) -> String {
    if err == CUDA_SUCCESS {
        return "success".to_string();
    }
    unsafe {
        let ptr = cudaGetErrorString(err);
        if ptr.is_null() {
            format!("CUDA error {}", err)
        } else {
            std::ffi::CStr::from_ptr(ptr).to_string_lossy().into_owned()
        }
    }
}

fn check_cuda(err: CudaError, context: &str) {
    if err != CUDA_SUCCESS {
        panic!("CUDA error in {}: {} (code {})", context, cuda_error_string(err), err);
    }
}

/// RAII wrapper for GPU device memory.
struct GpuMem {
    ptr: *mut std::ffi::c_void,
    size: usize,
}

impl GpuMem {
    fn alloc(size: usize) -> Self {
        let mut ptr: *mut std::ffi::c_void = std::ptr::null_mut();
        check_cuda(unsafe { cudaMalloc(&mut ptr, size) }, "cudaMalloc");
        GpuMem { ptr, size }
    }

    fn upload<T>(&self, data: &[T]) {
        let bytes = data.len() * std::mem::size_of::<T>();
        assert!(bytes <= self.size, "upload size {} exceeds allocation {}", bytes, self.size);
        check_cuda(
            unsafe { cudaMemcpy(self.ptr, data.as_ptr() as *const _, bytes, CUDA_MEMCPY_H2D) },
            "cudaMemcpy H2D",
        );
    }

    fn download<T: Copy + Default>(&self, count: usize) -> Vec<T> {
        let bytes = count * std::mem::size_of::<T>();
        assert!(bytes <= self.size, "download size {} exceeds allocation {}", bytes, self.size);
        let mut buf = vec![T::default(); count];
        check_cuda(
            unsafe { cudaMemcpy(buf.as_mut_ptr() as *mut _, self.ptr, bytes, CUDA_MEMCPY_D2H) },
            "cudaMemcpy D2H",
        );
        buf
    }

}

impl Drop for GpuMem {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe { cudaFree(self.ptr) };
            self.ptr = std::ptr::null_mut();
        }
    }
}

fn gpu_mem_info() -> (usize, usize) {
    let mut free: usize = 0;
    let mut total: usize = 0;
    check_cuda(unsafe { cudaMemGetInfo(&mut free, &mut total) }, "cudaMemGetInfo");
    (free, total)
}

// ═══════════════════════════════════════════════════════════════════════════
// Section 3: GpuFloat trait — dispatch to S/D variants
// ═══════════════════════════════════════════════════════════════════════════

trait GpuFloat: Copy + Send + Sync + Default + std::fmt::Display + 'static {
    fn from_i32(v: i32) -> Self;
    fn to_f64(self) -> f64;
    fn name() -> &'static str;
    fn bytes() -> usize;

    fn potrf_buffer_size(handle: CusolverDnHandle, n: i32, a: *const std::ffi::c_void, lda: i32) -> i32;
    fn potrf(handle: CusolverDnHandle, n: i32, a: *mut std::ffi::c_void, lda: i32,
             workspace: *mut std::ffi::c_void, lwork: i32, dev_info: *mut i32);
    fn trsm(handle: CublasHandle, m: i32, n: i32, alpha: f64,
            a: *const std::ffi::c_void, lda: i32,
            b: *mut std::ffi::c_void, ldb: i32);
}

impl GpuFloat for f32 {
    #[inline] fn from_i32(v: i32) -> Self { v as f32 }
    #[inline] fn to_f64(self) -> f64 { self as f64 }
    fn name() -> &'static str { "f32" }
    fn bytes() -> usize { 4 }

    fn potrf_buffer_size(handle: CusolverDnHandle, n: i32, a: *const std::ffi::c_void, lda: i32) -> i32 {
        let mut lwork: i32 = 0;
        check_cuda(
            unsafe { cusolverDnSpotrf_bufferSize(handle, CUBLAS_FILL_MODE_LOWER, n, a, lda, &mut lwork) },
            "cusolverDnSpotrf_bufferSize",
        );
        lwork
    }

    fn potrf(handle: CusolverDnHandle, n: i32, a: *mut std::ffi::c_void, lda: i32,
             workspace: *mut std::ffi::c_void, lwork: i32, dev_info: *mut i32) {
        check_cuda(
            unsafe { cusolverDnSpotrf(handle, CUBLAS_FILL_MODE_LOWER, n, a, lda, workspace, lwork, dev_info) },
            "cusolverDnSpotrf",
        );
    }

    fn trsm(handle: CublasHandle, m: i32, n: i32, alpha: f64,
            a: *const std::ffi::c_void, lda: i32,
            b: *mut std::ffi::c_void, ldb: i32) {
        let alpha_f32 = alpha as f32;
        check_cuda(
            unsafe {
                cublasStrsm_v2(
                    handle, CUBLAS_SIDE_LEFT, CUBLAS_FILL_MODE_LOWER, CUBLAS_OP_T,
                    CUBLAS_DIAG_NON_UNIT, m, n, &alpha_f32, a, lda, b, ldb,
                )
            },
            "cublasStrsm_v2",
        );
    }
}

impl GpuFloat for f64 {
    #[inline] fn from_i32(v: i32) -> Self { v as f64 }
    #[inline] fn to_f64(self) -> f64 { self }
    fn name() -> &'static str { "f64" }
    fn bytes() -> usize { 8 }

    fn potrf_buffer_size(handle: CusolverDnHandle, n: i32, a: *const std::ffi::c_void, lda: i32) -> i32 {
        let mut lwork: i32 = 0;
        check_cuda(
            unsafe { cusolverDnDpotrf_bufferSize(handle, CUBLAS_FILL_MODE_LOWER, n, a, lda, &mut lwork) },
            "cusolverDnDpotrf_bufferSize",
        );
        lwork
    }

    fn potrf(handle: CusolverDnHandle, n: i32, a: *mut std::ffi::c_void, lda: i32,
             workspace: *mut std::ffi::c_void, lwork: i32, dev_info: *mut i32) {
        check_cuda(
            unsafe { cusolverDnDpotrf(handle, CUBLAS_FILL_MODE_LOWER, n, a, lda, workspace, lwork, dev_info) },
            "cusolverDnDpotrf",
        );
    }

    fn trsm(handle: CublasHandle, m: i32, n: i32, alpha: f64,
            a: *const std::ffi::c_void, lda: i32,
            b: *mut std::ffi::c_void, ldb: i32) {
        check_cuda(
            unsafe {
                cublasDtrsm_v2(
                    handle, CUBLAS_SIDE_LEFT, CUBLAS_FILL_MODE_LOWER, CUBLAS_OP_T,
                    CUBLAS_DIAG_NON_UNIT, m, n, &alpha, a, lda, b, ldb,
                )
            },
            "cublasDtrsm_v2",
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Section 4: Graph generation (from certificate.rs)
// ═══════════════════════════════════════════════════════════════════════════

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

fn compute_j_coeff(c1: i32, c2: i32, d: usize, n: usize) -> i32 {
    let deficit = c2 * (d * d) as i32 - c1;
    if deficit < 0 { 1 } else { deficit / n as i32 + 2 }
}

// ═══════════════════════════════════════════════════════════════════════════
// Section 5: M formation — column-major for CUDA
// ═══════════════════════════════════════════════════════════════════════════

/// Compute M = c₁I - c₂B² + c₃J as a flat column-major Vec<F>.
/// Since M is symmetric, row-major and column-major are the same matrix
/// when stored as M[row * n + col] == M[col * n + row].
fn compute_m_colmajor<F: GpuFloat>(
    neighbors: &[usize], n: usize, d: usize, c1: i32, c2: i32, c3: i32,
) -> Vec<F> {
    use rayon::prelude::*;

    let mut m = vec![F::from_i32(0); n * n];

    // Compute in parallel by row
    let m_ptr = m.as_mut_ptr() as usize;
    (0..n).into_par_iter().for_each(|v| {
        let mut b2_row = vec![0i32; n];
        for p in 0..d {
            let u = neighbors[v * d + p];
            for q in 0..d {
                b2_row[neighbors[u * d + q]] += 1;
            }
        }
        for w in 0..n {
            let diag = if v == w { c1 } else { 0 };
            let val = F::from_i32(diag - c2 * b2_row[w] + c3);
            // Column-major: M[v, w] goes to offset w * n + v
            unsafe {
                *(m_ptr as *mut F).add(w * n + v) = val;
            }
        }
    });

    m
}

// ═══════════════════════════════════════════════════════════════════════════
// Section 6: Pack / refine / verify (adapted from certificate.rs)
// ═══════════════════════════════════════════════════════════════════════════

/// Pack TRSM solution (column-major flat array) into i32 z_packed for columns [col_start..col_end).
/// `sol` is column-major n × b_cols, `diag` has the diagonal of L.
fn pack_block<F: GpuFloat>(
    sol: &[F], n: usize, diag: &[F], col_start: usize, col_end: usize, scale: i32,
) -> (Vec<i32>, f64) {
    use rayon::prelude::*;

    let b_cols = col_end - col_start;
    let block_packed_len = col_end * (col_end + 1) / 2 - col_start * (col_start + 1) / 2;
    let block_offset = col_start * (col_start + 1) / 2;
    let mut packed = vec![0i32; block_packed_len];
    let packed_ptr = packed.as_mut_ptr() as usize;

    let block_max: f64 = (0..b_cols)
        .into_par_iter()
        .map(|k| {
            let j = col_start + k;
            let col_off = j * (j + 1) / 2 - block_offset;
            let l_jj = diag[j].to_f64();
            let s = scale as f64;
            let mut local_max: f64 = 0.0;
            for i in 0..j {
                // Column-major: sol[i, k] = sol[k * n + i]
                let z_val = sol[k * n + i].to_f64() * l_jj;
                let abs_z = z_val.abs();
                if abs_z > local_max { local_max = abs_z; }
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

// ═══════════════════════════════════════════════════════════════════════════
// Section 7: Base85 encoding + I/O
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
// Section 8: GPU pipeline
// ═══════════════════════════════════════════════════════════════════════════

fn run_gpu_pipeline<F: GpuFloat>(cfg: &Config) {
    let n = cfg.n;
    let d = cfg.d;
    let scale = cfg.scale;
    let block_size = cfg.block_size;

    let c3 = compute_j_coeff(cfg.c1, cfg.c2, d, n);
    let beta_num = (cfg.c1 as f64 / cfg.c2 as f64).sqrt();
    let beta = beta_num / d as f64;
    let elem_bytes = F::bytes();

    eprintln!("=== GPU Certificate Generator ===");
    eprintln!("Parameters: n={n}, d={d}, seed={}, scale={}, precision={}",
        cfg.seed, scale, F::name());
    eprintln!("Refinement passes: {}", cfg.refine);
    eprintln!("TRSM block size: {block_size}");
    eprintln!("M = {}I - {}B² + {c3}J", cfg.c1, cfg.c2);
    eprintln!("Spectral gap bound: β = √({}/{})/{d} = {beta:.6}", cfg.c1, cfg.c2);
    eprintln!("  (β·d = {beta_num:.6}, Alon-Boppana: 2√(d-1) = {:.6})",
        2.0 * ((d as f64) - 1.0).sqrt());

    // GPU memory info
    let (gpu_free, gpu_total) = gpu_mem_info();
    eprintln!("GPU memory: {} free / {} total",
        fmt_bytes(gpu_free as u64), fmt_bytes(gpu_total as u64));

    let m_bytes = n * n * elem_bytes;
    eprintln!("M size: {} ({})", fmt_bytes(m_bytes as u64), F::name());
    if m_bytes > gpu_free {
        panic!("M ({}) exceeds available GPU memory ({})!",
            fmt_bytes(m_bytes as u64), fmt_bytes(gpu_free as u64));
    }

    let t_total = Instant::now();

    // Step 1: Generate random regular graph
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

    // Step 2: Compute M (CPU, column-major)
    eprintln!("Computing M ({} {})...", fmt_bytes(m_bytes as u64), F::name());
    let t0 = Instant::now();
    let m_host = compute_m_colmajor::<F>(&neighbors, n, d, cfg.c1, cfg.c2, c3);
    eprintln!("  M[0,0] = {} [{}]", m_host[0], fmt_duration(t0.elapsed()));

    // Step 3: Upload M to GPU
    eprintln!("Uploading M to GPU...");
    let t0 = Instant::now();
    let d_m = GpuMem::alloc(m_bytes);
    d_m.upload(&m_host);
    drop(m_host);
    check_cuda(unsafe { cudaDeviceSynchronize() }, "sync after upload");
    eprintln!("  Uploaded [{}]", fmt_duration(t0.elapsed()));

    // Step 4: Cholesky factorization (GPU)
    eprintln!("Cholesky factorization ({}, GPU)...", F::name());
    let t0 = Instant::now();

    let mut solver_handle: CusolverDnHandle = std::ptr::null_mut();
    check_cuda(unsafe { cusolverDnCreate(&mut solver_handle) }, "cusolverDnCreate");

    let lwork = F::potrf_buffer_size(solver_handle, n as i32, d_m.ptr, n as i32);
    eprintln!("  Workspace: {} ({} elements)", fmt_bytes(lwork as u64 * elem_bytes as u64), lwork);

    let d_workspace = GpuMem::alloc(lwork as usize * elem_bytes);
    let d_info = GpuMem::alloc(std::mem::size_of::<i32>());

    F::potrf(solver_handle, n as i32, d_m.ptr, n as i32,
             d_workspace.ptr, lwork, d_info.ptr as *mut i32);

    check_cuda(unsafe { cudaDeviceSynchronize() }, "sync after potrf");

    // Check devInfo
    let info_val: Vec<i32> = d_info.download(1);
    if info_val[0] != 0 {
        if info_val[0] > 0 {
            panic!("Cholesky failed: M is not positive definite (leading minor {} is not positive)", info_val[0]);
        } else {
            panic!("Cholesky failed: parameter {} is invalid", -info_val[0]);
        }
    }
    eprintln!("  Cholesky succeeded [{}]", fmt_duration(t0.elapsed()));

    drop(d_workspace);
    drop(d_info);
    check_cuda(unsafe { cusolverDnDestroy(solver_handle) }, "cusolverDnDestroy");

    // Step 5: Extract L diagonal via cublasGetVector (single strided DMA)
    eprintln!("Extracting L diagonal...");
    let t0 = Instant::now();
    let mut diag: Vec<F> = vec![F::from_i32(0); n];
    check_cuda(
        unsafe {
            cublasGetVector(
                n as i32, elem_bytes as i32,
                d_m.ptr, (n + 1) as i32,          // stride n+1 on device (diagonal)
                diag.as_mut_ptr() as *mut _, 1,    // stride 1 on host (contiguous)
            )
        },
        "cublasGetVector (diagonal)",
    );
    eprintln!("  L[0,0] = {:.6} [{}]", diag[0].to_f64(), fmt_duration(t0.elapsed()));

    // Step 6: Streaming TRSM + pack + refine + verify
    let total = n * (n + 1) / 2;

    eprintln!("Streaming TRSM + refine + verify ({} packed i32)...",
        fmt_bytes(total as u64 * 4));
    let t0 = Instant::now();

    // Create cuBLAS handle
    let mut cublas_handle: CublasHandle = std::ptr::null_mut();
    check_cuda(unsafe { cublasCreate_v2(&mut cublas_handle) }, "cublasCreate_v2");

    // Allocate GPU buffer for RHS/solution
    let rhs_bytes = n * block_size * elem_bytes;
    let d_rhs = GpuMem::alloc(rhs_bytes);

    fs::create_dir_all(&cfg.out).expect("Cannot create output dir");
    let cert_path = cfg.out.join("cert_z.b85");
    let cert_file = fs::File::create(&cert_path)
        .unwrap_or_else(|e| panic!("Cannot create {}: {}", cert_path.display(), e));
    let mut cert_writer = std::io::BufWriter::new(cert_file);

    let mut z_max_offdiag: f64 = 0.0;
    let mut global_min_diag: i64 = i64::MAX;
    let mut global_eps_max: i64 = 0;
    let mut total_entries: usize = 0;
    let mut trsm_time_total = std::time::Duration::ZERO;
    let mut pack_time_total = std::time::Duration::ZERO;

    let num_blocks = (n + block_size - 1) / block_size;

    for b_idx in 0..num_blocks {
        let b_start = b_idx * block_size;
        let b_end = (b_start + block_size).min(n);
        let b_cols = b_end - b_start;

        // Create identity RHS on host (column-major: col k has 1 at row b_start+k)
        let mut rhs_host = vec![F::from_i32(0); n * b_cols];
        for k in 0..b_cols {
            rhs_host[k * n + b_start + k] = F::from_i32(1);
        }

        // Upload RHS
        d_rhs.upload(&rhs_host[..n * b_cols]);
        drop(rhs_host);

        // GPU TRSM: solve L^T * X = I_block, result overwrites d_rhs
        let t_trsm = Instant::now();
        F::trsm(cublas_handle, n as i32, b_cols as i32, 1.0,
                d_m.ptr, n as i32, d_rhs.ptr, n as i32);
        check_cuda(unsafe { cudaDeviceSynchronize() }, "sync after trsm");
        trsm_time_total += t_trsm.elapsed();

        // Download solution
        let sol: Vec<F> = d_rhs.download(n * b_cols);

        // Pack to i32
        let t_pack = Instant::now();
        let (mut packed_block, block_max) = pack_block(&sol, n, &diag, b_start, b_end, scale);
        z_max_offdiag = z_max_offdiag.max(block_max);
        drop(sol);

        assert!(
            (z_max_offdiag * scale as f64) < i32::MAX as f64,
            "Z entries overflow i32! Reduce --scale."
        );

        // Refine
        for _ in 0..cfg.refine {
            refine_columns(&mut packed_block, b_start, b_end, &neighbors, n, d,
                cfg.c1, cfg.c2, c3);
        }

        // Verify
        let (block_min, block_eps) =
            verify_columns(&packed_block, b_start, b_end, &neighbors, n, d,
                cfg.c1, cfg.c2, c3);
        global_min_diag = global_min_diag.min(block_min);
        global_eps_max = global_eps_max.max(block_eps);
        pack_time_total += t_pack.elapsed();

        // Write base85
        {
            use std::io::Write;
            let encoded = encode_base85(&packed_block);
            cert_writer.write_all(&encoded)
                .unwrap_or_else(|e| panic!("Write failed: {}", e));
        }
        total_entries += packed_block.len();

        if num_blocks > 1 {
            eprintln!("  Block {}/{}: cols [{}, {}), trsm={}, pack+refine+verify={}",
                b_idx + 1, num_blocks, b_start, b_end,
                fmt_duration(trsm_time_total / (b_idx as u32 + 1)),
                fmt_duration(pack_time_total / (b_idx as u32 + 1)));
        }
    }

    {
        use std::io::Write;
        cert_writer.flush().unwrap();
    }
    drop(cert_writer);

    // Clean up GPU resources
    drop(d_rhs);
    drop(d_m);
    check_cuda(unsafe { cublasDestroy_v2(cublas_handle) }, "cublasDestroy_v2");

    let stream_time = t0.elapsed();
    eprintln!("  TRSM total: {}", fmt_duration(trsm_time_total));
    eprintln!("  Pack+refine+verify total: {}", fmt_duration(pack_time_total));
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
    eprintln!("  cert_z.b85: {} ({} entries, {} base85)",
        fmt_bytes(total_entries as u64 * 4), total_entries,
        fmt_bytes(total_entries as u64 * 5));

    eprintln!("---");
    eprintln!("Total time: {}", fmt_duration(t_total.elapsed()));
    if let Some(rss) = peak_rss_bytes() {
        eprintln!("Peak RSS: {}", fmt_bytes(rss));
    }
    eprintln!("Done! Generated {}", cfg.out.display());
}

// ═══════════════════════════════════════════════════════════════════════════
// Section 9: Utilities, Config, CLI, main
// ═══════════════════════════════════════════════════════════════════════════

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

#[allow(dead_code)]
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
    block_size: usize,
    gpu_id: i32,
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
    let block_size: usize = parse_flag(&args, "--block").unwrap_or(2048);
    let gpu_id: i32 = parse_flag(&args, "--gpu").unwrap_or(0);
    let out: PathBuf = parse_flag::<String>(&args, "--out")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(&format!("data/{n}")));

    // Set GPU device
    check_cuda(unsafe { cudaSetDevice(gpu_id) }, "cudaSetDevice");

    let cfg = Config { n, d, seed, scale, out, c1, c2, refine, use_f64, block_size, gpu_id };

    if cfg.use_f64 {
        run_gpu_pipeline::<f64>(&cfg);
    } else {
        run_gpu_pipeline::<f32>(&cfg);
    }
}
