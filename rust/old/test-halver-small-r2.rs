// OBSOLETE: Small r² halver contradiction; path was deleted.
#!/usr/bin/env -S cargo +nightly -Zscript
//! Test whether the halver contradiction works for r² = ((q+1)/q)² with large q.
//! This is the effective r² from the regular-Tanner-on-preimage approach.

fn check_contradiction(r2: f64, beta: f64, eps: f64, m_max: i64) -> bool {
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

fn main() {
    println!("=== Testing s > ε·k contradicts s·m ≤ r²·(k-s)·(s + β²(m-s)) ===");
    println!("where r² = ((q+1)/q)² for various q (number of fibers)\n");

    println!("{:>4} {:>12} {:>8} {:>12} {:>10}", "q", "r²=(q+1/q)²", "β", "ε=r²·β", "works?");
    println!("{}", "-".repeat(52));

    for q in [1_u64, 2, 4, 8, 16, 32, 64, 128] {
        let r2 = ((q + 1) as f64 / q as f64).powi(2);
        for beta_pct in [1, 5, 10, 20] {
            let beta = beta_pct as f64 / 100.0;
            let eps = r2 * beta;
            if eps >= 1.0 { continue; }
            let ok = check_contradiction(r2, beta, eps, 500);
            println!("{:4} {:12.4} {:8.2} {:12.4} {:>10}", q, r2, beta, eps, if ok { "OK" } else { "FAIL" });
        }
        println!();
    }

    // For D=2, B=16: q can range from 16 to B²=256
    println!("\n=== Application: D=2, B=16, various q ===");
    println!("In application: β = c^(2^l) < 1/4\n");
    for q in [16_u64, 32, 64, 128, 256] {
        let r2 = ((q + 1) as f64 / q as f64).powi(2);
        for beta_pct in [1, 5, 10, 24] {
            let beta = beta_pct as f64 / 100.0;
            let eps = r2 * beta;
            if eps >= 1.0 { continue; }
            let ok = check_contradiction(r2, beta, eps, 1000);
            println!("  q={:3}, r²={:.4}, β={:.2}: ε=r²β={:.4} → {}",
                q, r2, beta, eps, if ok { "OK" } else { "FAIL" });
        }
    }

    // What's the minimum q for which r²·β < 1 and contradiction works?
    println!("\n=== Minimum q for contradiction to work ===");
    for beta_pct in [1, 5, 10, 20, 24] {
        let beta = beta_pct as f64 / 100.0;
        let mut min_q = 0;
        for q in 1..=10000_u64 {
            let r2 = ((q + 1) as f64 / q as f64).powi(2);
            let eps = r2 * beta;
            if eps >= 1.0 { continue; }
            if check_contradiction(r2, beta, eps, 500) {
                min_q = q;
                break;
            }
        }
        println!("  β={:.2}: min q={}", beta, min_q);
    }

    // Alternative approach: what ε works for various r² values?
    // Find the tight threshold via binary search
    println!("\n=== Tight threshold: max ε (mult of β) for contradiction to work ===");
    for r2_100 in [100_u32, 110, 120, 130, 150, 200, 400, 900] {
        let r2 = r2_100 as f64 / 100.0;
        for beta_pct in [1, 5, 10] {
            let beta = beta_pct as f64 / 100.0;
            // Binary search for max mult such that mult*beta works as ε
            let mut lo = 0.0_f64;
            let mut hi = 1.0 / beta;
            for _ in 0..50 {
                let mid = (lo + hi) / 2.0;
                let eps = mid * beta;
                if eps >= 1.0 || !check_contradiction(r2, beta, eps, 200) {
                    hi = mid;
                } else {
                    lo = mid;
                }
            }
            println!("  r²={:.2}, β={:.2}: max mult = {:.2}, max ε = {:.4}", r2, beta, lo, lo * beta);
        }
    }
}
