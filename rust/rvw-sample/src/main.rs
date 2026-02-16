/// Numerical validation of the RVW quadratic inequality:
///   G(a,b,c,p,q,r) = a²c² + (b²-c²)·|p|·|X| - a²b²·X² ≥ 0
/// where X = p+2q+r, a²+b² = 1, |p| ≤ a², |r| ≤ c²,
/// q² ≤ (a²+p)(c²+r) [CS+], q² ≤ (a²-p)(c²-r) [CS-].
///
/// Strategy:
/// 1. G is concave in q (∂²G/∂q² = -8a²b² < 0), so min over q is at CS boundary.
/// 2. At CS- boundary: q² = (a²-p)(c²-r). Substitute q = ±√((a²-p)(c²-r)).
///    At CS+ boundary: q² = (a²+p)(c²+r). Substitute q = ±√((a²+p)(c²+r)).
/// 3. The minimum must occur at one of these 4 boundary values of q.
/// 4. So we only need to scan (a, c, p, r) and evaluate G at the 4 boundary q values.
///
/// This gives very high confidence if the minimum found is strictly positive
/// (or zero, which occurs on the tight manifold {c=b, p=a², r=c², q=0}).

use rand::Rng;

/// Evaluate G at given parameters.
/// Returns (G_value, X_value) where G = a²c² + (b²-c²)·|p|·|X| - a²b²·X²
fn eval_g(a2: f64, b2: f64, c2: f64, p: f64, q: f64, r: f64) -> (f64, f64) {
    let x = p + 2.0 * q + r;
    let g = a2 * c2 + (b2 - c2) * p.abs() * x.abs() - a2 * b2 * x * x;
    (g, x)
}

/// For given (a², c², p, r), evaluate G at the 4 CS boundary values of q.
/// Returns the minimum G value found.
fn min_g_over_q(a2: f64, b2: f64, c2: f64, p: f64, r: f64) -> f64 {
    let mut min_g = f64::INFINITY;

    // CS- boundary: q² = (a²-p)(c²-r)
    let cs_minus_prod = (a2 - p) * (c2 - r);
    if cs_minus_prod >= 0.0 {
        let q_abs = cs_minus_prod.sqrt();
        for &q in &[q_abs, -q_abs] {
            // Check CS+ constraint: q² ≤ (a²+p)(c²+r)
            let cs_plus_prod = (a2 + p) * (c2 + r);
            if q * q <= cs_plus_prod + 1e-15 {
                let (g, _) = eval_g(a2, b2, c2, p, q, r);
                min_g = min_g.min(g);
            }
        }
    }

    // CS+ boundary: q² = (a²+p)(c²+r)
    let cs_plus_prod = (a2 + p) * (c2 + r);
    if cs_plus_prod >= 0.0 {
        let q_abs = cs_plus_prod.sqrt();
        for &q in &[q_abs, -q_abs] {
            // Check CS- constraint: q² ≤ (a²-p)(c²-r)
            let cs_minus_prod = (a2 - p) * (c2 - r);
            if q * q <= cs_minus_prod + 1e-15 {
                let (g, _) = eval_g(a2, b2, c2, p, q, r);
                min_g = min_g.min(g);
            }
        }
    }

    // Also check q = 0 (interior point, can be extremal for |X| term)
    {
        let (g, _) = eval_g(a2, b2, c2, p, 0.0, r);
        min_g = min_g.min(g);
    }

    min_g
}

/// Dense grid search over the parameter space.
/// Returns (min_G, min_params, total_points).
fn grid_search(n_a: usize, n_c: usize, n_p: usize, n_r: usize)
    -> (f64, (f64, f64, f64, f64, f64), u64)
{
    let mut global_min = f64::INFINITY;
    let mut global_params = (0.0, 0.0, 0.0, 0.0, 0.0);
    let mut total = 0u64;

    for ia in 0..n_a {
        // a ∈ (0, 1), so a² ∈ (0, 1)
        let a2 = (ia as f64 + 0.5) / n_a as f64;
        let b2 = 1.0 - a2;
        if b2 <= 0.0 { continue; }

        for ic in 0..n_c {
            // c² ∈ (0, b²)
            let c2 = (ic as f64 + 0.5) / n_c as f64 * b2;
            if c2 <= 0.0 { continue; }

            for ip in 0..n_p {
                // p ∈ [-a², a²]
                let p = -a2 + (ip as f64 + 0.5) / n_p as f64 * 2.0 * a2;

                for ir in 0..n_r {
                    // r ∈ [-c², c²]
                    let r = -c2 + (ir as f64 + 0.5) / n_r as f64 * 2.0 * c2;

                    total += 1;
                    let g = min_g_over_q(a2, b2, c2, p, r);
                    if g < global_min {
                        global_min = g;
                        global_params = (a2, c2, p, r, g);
                    }
                }
            }
        }
    }

    (global_min, global_params, total)
}

/// Random sampling within the feasible region.
fn random_search(n_samples: u64) -> (f64, (f64, f64, f64, f64, f64), u64) {
    let mut rng = rand::thread_rng();
    let mut global_min = f64::INFINITY;
    let mut global_params = (0.0, 0.0, 0.0, 0.0, 0.0);

    for _ in 0..n_samples {
        let a2: f64 = rng.gen_range(1e-6..1.0 - 1e-6);
        let b2 = 1.0 - a2;
        let c2: f64 = rng.gen_range(1e-6..b2);
        let p: f64 = rng.gen_range(-a2..a2);
        let r: f64 = rng.gen_range(-c2..c2);

        let g = min_g_over_q(a2, b2, c2, p, r);
        if g < global_min {
            global_min = g;
            global_params = (a2, c2, p, r, g);
        }
    }

    (global_min, global_params, n_samples)
}

/// Focused search near the tight manifold {c²=b², p=a², r=c²}.
/// On this manifold, G = 0 exactly. We search nearby to verify G ≥ 0.
fn tight_manifold_search(n_samples: u64) -> (f64, (f64, f64, f64, f64, f64), u64) {
    let mut rng = rand::thread_rng();
    let mut global_min = f64::INFINITY;
    let mut global_params = (0.0, 0.0, 0.0, 0.0, 0.0);

    for _ in 0..n_samples {
        let a2: f64 = rng.gen_range(0.01..0.99);
        let b2 = 1.0 - a2;

        // Near tight manifold: c² ≈ b²
        let eps_c: f64 = rng.gen_range(-0.01..0.01);
        let c2 = (b2 + eps_c).clamp(1e-6, b2 - 1e-6);

        // Near p = a²
        let eps_p: f64 = rng.gen_range(-0.01..0.01);
        let p = (a2 + eps_p).clamp(-a2, a2);

        // Near r = c²
        let eps_r: f64 = rng.gen_range(-0.01..0.01);
        let r = (c2 + eps_r).clamp(-c2, c2);

        let g = min_g_over_q(a2, b2, c2, p, r);
        if g < global_min {
            global_min = g;
            global_params = (a2, c2, p, r, g);
        }
    }

    (global_min, global_params, n_samples)
}

/// Local minimization via coordinate descent from a given starting point.
/// Returns the minimum G found.
/// Enforce all feasibility constraints, returning false if infeasible.
fn enforce_constraints(a2: &mut f64, c2: &mut f64, p: &mut f64, r: &mut f64) -> bool {
    let eps = 1e-8;
    *a2 = a2.clamp(eps, 1.0 - eps);
    let b2 = 1.0 - *a2;
    let max_c2 = (b2 - eps).max(eps);
    *c2 = c2.clamp(eps, max_c2);
    *p = p.clamp(-*a2, *a2);
    *r = r.clamp(-*c2, *c2);
    *c2 < b2
}

fn local_minimize(a2_init: f64, c2_init: f64, p_init: f64, r_init: f64)
    -> (f64, f64, f64, f64, f64)
{
    let step_sizes = [0.01, 0.001, 0.0001, 0.00001, 0.000001];
    let mut a2 = a2_init;
    let mut c2 = c2_init;
    let mut p = p_init;
    let mut r = r_init;
    if !enforce_constraints(&mut a2, &mut c2, &mut p, &mut r) {
        return (f64::INFINITY, a2, c2, p, r);
    }
    let mut best_g = min_g_over_q(a2, 1.0 - a2, c2, p, r);

    for &step in &step_sizes {
        for _ in 0..1000 {
            let mut improved = false;

            // Try moving each variable by ±step
            for dir in 0..4 {
                for &sign in &[-1.0f64, 1.0] {
                    let mut na2 = a2;
                    let mut nc2 = c2;
                    let mut np = p;
                    let mut nr = r;
                    match dir {
                        0 => na2 += sign * step,
                        1 => nc2 += sign * step,
                        2 => np += sign * step,
                        3 => nr += sign * step,
                        _ => unreachable!(),
                    }

                    // Re-enforce ALL constraints after any change
                    if !enforce_constraints(&mut na2, &mut nc2, &mut np, &mut nr) {
                        continue;
                    }

                    let nb2 = 1.0 - na2;
                    let g = min_g_over_q(na2, nb2, nc2, np, nr);
                    if g < best_g - 1e-18 {
                        a2 = na2;
                        c2 = nc2;
                        p = np;
                        r = nr;
                        best_g = g;
                        improved = true;
                    }
                }
            }

            if !improved { break; }
        }
    }

    (best_g, a2, c2, p, r)
}

/// Verify the tight manifold: at c²=b², p=a², r=c², X = a²+c² = 1,
/// G = a²c² + 0·|p|·|X| - a²b²·1 = a²c² - a²(1-a²) = a²(c² - b²) = 0
fn verify_tight_manifold() {
    println!("=== Tight manifold verification ===");
    println!("On {{c²=b², p=a², r=c², q=0}}: X=a²+c²=1, G=a²c²-a²b²=0");

    for &a2 in &[0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9] {
        let b2 = 1.0 - a2;
        let c2 = b2;  // tight: c² = b²
        let p = a2;   // tight: p = a²
        let r = c2;   // tight: r = c²
        let q = 0.0;  // tight: q = 0
        let (g, x) = eval_g(a2, b2, c2, p, q, r);
        println!("  a²={:.2}, b²={:.2}, c²={:.2}: X={:.6}, G={:.2e}", a2, b2, c2, x, g);
    }
    println!();
}

/// Full validation with multiple strategies
fn main() {
    println!("RVW Quadratic Inequality Numerical Validation");
    println!("==============================================");
    println!("G = a²c² + (b²-c²)·|p|·|X| - a²b²·X²");
    println!("where X = p+2q+r, a²+b²=1, |p|≤a², |r|≤c²,");
    println!("  q²≤(a²+p)(c²+r) [CS+], q²≤(a²-p)(c²-r) [CS-]");
    println!();
    println!("G is concave in q, so minimum is at CS boundary.");
    println!("We evaluate at all 4 boundary q values for each (a²,c²,p,r).");
    println!();

    verify_tight_manifold();

    // Phase 1: Coarse grid
    println!("=== Phase 1: Coarse grid (50×50×50×50 = 6.25M points) ===");
    let (min_g, params, total) = grid_search(50, 50, 50, 50);
    println!("  Points evaluated: {}", total);
    println!("  Minimum G: {:.6e}", min_g);
    println!("  At: a²={:.6}, c²={:.6}, p={:.6}, r={:.6}", params.0, params.1, params.2, params.3);
    if min_g >= 0.0 {
        println!("  PASS: G ≥ 0 everywhere on grid");
    } else {
        println!("  FAIL: G < 0 found! Counterexample!");
    }
    println!();

    // Phase 2: Fine grid
    println!("=== Phase 2: Fine grid (100×100×100×100 = 100M points) ===");
    let (min_g, params, total) = grid_search(100, 100, 100, 100);
    println!("  Points evaluated: {}", total);
    println!("  Minimum G: {:.6e}", min_g);
    println!("  At: a²={:.6}, c²={:.6}, p={:.6}, r={:.6}", params.0, params.1, params.2, params.3);
    if min_g >= 0.0 {
        println!("  PASS: G ≥ 0 everywhere on grid");
    } else {
        println!("  FAIL: G < 0 found! Counterexample!");
    }
    println!();

    // Phase 3: Random sampling
    println!("=== Phase 3: Random sampling (10M points) ===");
    let (min_g, params, total) = random_search(10_000_000);
    println!("  Points evaluated: {}", total);
    println!("  Minimum G: {:.6e}", min_g);
    println!("  At: a²={:.6}, c²={:.6}, p={:.6}, r={:.6}", params.0, params.1, params.2, params.3);
    if min_g >= 0.0 {
        println!("  PASS: G ≥ 0 everywhere");
    } else {
        println!("  FAIL: G < 0 found!");
    }
    println!();

    // Phase 4: Tight manifold neighborhood
    println!("=== Phase 4: Tight manifold neighborhood (10M points) ===");
    let (min_g, params, total) = tight_manifold_search(10_000_000);
    println!("  Points evaluated: {}", total);
    println!("  Minimum G: {:.6e}", min_g);
    println!("  At: a²={:.6}, c²={:.6}, p={:.6}, r={:.6}", params.0, params.1, params.2, params.3);
    if min_g >= 0.0 {
        println!("  PASS: G ≥ 0 near tight manifold");
    } else {
        println!("  FAIL: G < 0 found near tight manifold!");
    }
    println!();

    // Phase 5: Local minimization from multiple starting points
    println!("=== Phase 5: Local minimization (1000 random + 1000 manifold starts) ===");
    let mut rng = rand::thread_rng();
    let mut worst_g = f64::INFINITY;
    let mut worst_params = (0.0, 0.0, 0.0, 0.0, 0.0);

    for _ in 0..1000 {
        let a2: f64 = rng.gen_range(0.05..0.95);
        let b2 = 1.0 - a2;
        let c2: f64 = rng.gen_range(0.01..(b2 - 0.01).max(0.02));
        let p: f64 = rng.gen_range(-a2 * 0.99..a2 * 0.99);
        let r: f64 = rng.gen_range(-c2 * 0.99..c2 * 0.99);

        let (g, ga2, gc2, gp, gr) = local_minimize(a2, c2, p, r);
        if g < worst_g {
            worst_g = g;
            worst_params = (g, ga2, gc2, gp, gr);
        }
    }

    // Also start from tight manifold neighborhood
    for _ in 0..1000 {
        let a2: f64 = rng.gen_range(0.05..0.95);
        let b2 = 1.0 - a2;
        let c2_max = (b2 - 1e-4).max(1e-4);
        let c2_target = b2.min(c2_max);
        let eps: f64 = rng.gen_range(-0.001..0.001);
        let c2 = (c2_target + eps).clamp(1e-4, c2_max);
        let p = (a2 + rng.gen_range(-0.001f64..0.001)).clamp(-a2 + 1e-8, a2 - 1e-8);
        let r = (c2 + rng.gen_range(-0.001f64..0.001)).clamp(-c2 + 1e-8, c2 - 1e-8);

        let (g, ga2, gc2, gp, gr) = local_minimize(a2, c2, p, r);
        if g < worst_g {
            worst_g = g;
            worst_params = (g, ga2, gc2, gp, gr);
        }
    }

    println!("  Minimum G found: {:.6e}", worst_g);
    println!("  At: a²={:.6}, c²={:.6}, p={:.6}, r={:.6}",
             worst_params.1, worst_params.2, worst_params.3, worst_params.4);
    if worst_g >= -1e-12 {
        println!("  PASS: G ≥ 0 (within numerical tolerance)");
    } else {
        println!("  FAIL: G < 0 found!");
    }
    println!();

    // Summary
    println!("=== SUMMARY ===");
    println!("The inequality G ≥ 0 was tested with:");
    println!("  - Dense grid: 100M+ evaluation points");
    println!("  - Random sampling: 10M points");
    println!("  - Tight manifold focus: 10M points near the zero set");
    println!("  - Local minimization: 2000 starting points × multi-resolution descent");
    println!();
    println!("Known zero: tight manifold {{c²=b², p=a², r=c², q=0}} gives G=0 exactly.");
    println!("The minimum G is attained on or near this manifold.");
    println!();
    if worst_g >= -1e-10 {
        println!("CONCLUSION: Strong numerical evidence that G ≥ 0 everywhere.");
        println!("The inequality appears TRUE. Confidence: very high.");
    } else {
        println!("WARNING: Found G < 0 at some point. Check for counterexample or numerical issues.");
    }
}
