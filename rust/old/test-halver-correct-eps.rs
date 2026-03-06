// OBSOLETE: Epsilon search for irregular graph halver; path was deleted.
#!/usr/bin/env -S cargo +nightly -Zscript
//! Find the correct ε for the irregular graph halver contradiction.
//!
//! Question: Given s·m ≤ r²·(k-s)·(s + β²·(m-s)) [Tanner bound for irregular graphs],
//! what is the largest ε such that s > ε·k always leads to contradiction?
//!
//! The theorem currently claims ε = r²·β. We test various ε candidates.

/// For given r², β, check if ε works as the halver bound:
/// does s > ε·k contradict s·m ≤ r²·(k-s)·(s+β²(m-s)) for ALL valid s,k,m?
fn check_eps(r2: f64, beta: f64, eps: f64, m_max: i64) -> bool {
    if eps >= 1.0 { return true; }
    for m in 2..=m_max {
        for k in 1..=m {
            let s_min = (eps * k as f64).floor() as i64 + 1;
            for s in s_min.max(1)..k.min(m + 1) {
                let sf = s as f64;
                let mf = m as f64;
                let kf = k as f64;
                let lhs = sf * mf;
                let rhs = r2 * (kf - sf) * (sf + beta * beta * (mf - sf));
                if lhs <= rhs + 1e-9 {
                    return false;
                }
            }
        }
    }
    true
}

/// Find the largest ε (in increments of 0.001) that works
fn find_max_eps(r2: f64, beta: f64, m_max: i64) -> f64 {
    let mut best = 0.0;
    // Search from high to low
    for e in (1..1000).rev() {
        let eps = e as f64 / 1000.0;
        if check_eps(r2, beta, eps, m_max) {
            best = eps;
            break;
        }
    }
    best
}

/// Analytical candidate: solve s·m = r²·(k-s)·(s + β²(m-s)) for s/k at k=m
/// Setting γ = s/k = s/m: γ·m² = r²·(1-γ)·m·(γ·m + β²·m·(1-γ))
///   γ = r²·(1-γ)·(γ + β²(1-γ))
///   γ = r²·(γ - γ² + β² - 2β²γ + β²γ²)
///   γ = r²·(β² + γ(1-2β²) - γ²(1-β²))
///   r²(1-β²)γ² + γ(1 - r²(1-2β²)) - r²β² = 0
/// Use quadratic formula.
fn analytical_threshold(r2: f64, beta: f64) -> f64 {
    let b2 = beta * beta;
    let a = r2 * (1.0 - b2);
    let b = 1.0 - r2 * (1.0 - 2.0 * b2);
    let c = -r2 * b2;
    let disc = b * b - 4.0 * a * c;
    if disc < 0.0 || a == 0.0 { return 0.0; }
    (-b + disc.sqrt()) / (2.0 * a)
}

fn main() {
    println!("=== Finding maximum achievable ε for irregular graph halver ===");
    println!("Tanner bound: s·m ≤ r²·(k-s)·(s + β²(m-s))");
    println!("Looking for largest ε such that s > ε·k always contradicts Tanner.\n");

    println!("{:>4} {:>6} {:>8} {:>10} {:>10} {:>10}", "r²", "β", "r²·β", "max ε(num)", "analytic", "r²·β ok?");
    println!("{}", "-".repeat(56));

    for r2 in [1.0_f64, 2.0, 4.0, 9.0] {
        for beta_pct in [1, 2, 5, 10, 15, 20, 24] {
            let beta = beta_pct as f64 / 100.0;
            let eps_claimed = r2 * beta;
            if eps_claimed >= 1.0 { continue; }
            let max_eps = find_max_eps(r2, beta, 500);
            let analytic = analytical_threshold(r2, beta);
            let claimed_ok = check_eps(r2, beta, eps_claimed, 500);
            println!("{:4.0} {:6.2} {:8.3} {:10.3} {:10.3} {:>10}",
                r2, beta, eps_claimed, max_eps, analytic,
                if claimed_ok { "YES" } else { "NO" });
        }
        println!();
    }

    // Focus on the application case: r²=4, small β
    println!("\n=== Application case: r²=4, small β ===");
    println!("Need ε to be proportional to β (not bounded away from 0).\n");
    for beta_pct in [1, 2, 5, 10, 15, 20, 24] {
        let beta = beta_pct as f64 / 100.0;
        let r2 = 4.0;
        let max_eps = find_max_eps(r2, beta, 1000);
        let ratio = if beta > 0.0 { max_eps / beta } else { 0.0 };
        let analytic = analytical_threshold(r2, beta);
        println!("  β={:.2}: max ε={:.3}, analytic γ*={:.3}, ratio ε/β={:.1}, 4β={:.3}",
            beta, max_eps, analytic, ratio, 4.0 * beta);
    }

    // Check if ε = β works (independent of r²)?
    println!("\n=== Does ε = β work (ignoring r² factor)? ===");
    for r2 in [2.0_f64, 4.0, 9.0] {
        for beta_pct in [1, 5, 10, 20] {
            let beta = beta_pct as f64 / 100.0;
            let ok = check_eps(r2, beta, beta, 500);
            println!("  r²={:.0}, β={:.2}: ε=β={:.2} → {}", r2, beta, beta, if ok { "OK" } else { "FAIL" });
        }
    }

    // Try ε = r·β (not r²·β)
    println!("\n=== Does ε = r·β work? ===");
    for r2 in [2.0_f64, 4.0, 9.0] {
        let r = r2.sqrt();
        for beta_pct in [1, 5, 10, 20] {
            let beta = beta_pct as f64 / 100.0;
            let eps = r * beta;
            if eps >= 1.0 { continue; }
            let ok = check_eps(r2, beta, eps, 500);
            println!("  r²={:.0}, r={:.1}, β={:.2}: ε=r·β={:.3} → {}",
                r2, r, beta, eps, if ok { "OK" } else { "FAIL" });
        }
    }

    // Key insight test: does the volume Tanner (no r² factor) with
    // ε = β work? The volume Tanner is: vol(T)·halfs ≤ vol(N(T))·(vol(T)+β²(halfs-vol(T)))
    // If we set σ = vol(T)/halfs, then σ ≤ vol(N(T))/halfs · (σ+β²(1-σ))
    // Edge mono gives vol(N(T)) ≤ sum of degrees of positions with output < k in top half
    // The "bad" thing is we can't bound vol(N(T)) tightly
    println!("\n=== Check: what ε works with Tanner using r²·β² instead of β² in the inner term? ===");
    println!("i.e., s·m ≤ r²·(k-s)·(s + (r²β²)(m-s)) — even worse");
    for r2 in [4.0_f64] {
        for beta_pct in [5, 10, 20] {
            let beta = beta_pct as f64 / 100.0;
            let eps = r2 * beta;
            // Use r²·β² instead of β²
            let mut ok = true;
            for m in 2..=500_i64 {
                for k in 1..=m {
                    let s_min = (eps * k as f64).floor() as i64 + 1;
                    for s in s_min.max(1)..k.min(m+1) {
                        let sf = s as f64;
                        let mf = m as f64;
                        let kf = k as f64;
                        let lhs = sf * mf;
                        let rhs = r2 * (kf - sf) * (sf + r2 * beta * beta * (mf - sf));
                        if lhs <= rhs + 1e-9 {
                            ok = false;
                        }
                    }
                }
            }
            println!("  r²=4, β={:.2}, ε=r²β={:.2}: {}", beta, eps, if ok { "OK" } else { "FAIL" });
        }
    }
}
