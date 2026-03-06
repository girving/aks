// OBSOLETE: Irregular graph halver contradiction; path was deleted (false theorem).
#!/usr/bin/env -S cargo +nightly -Zscript
//! Test whether the graph halver contradiction lemma holds:
//! Given s > r²·β·k, s < k ≤ m, 0 ≤ β, r²·β < 1,
//! is it always true that s·m > r²·(k-s)·(s + β²·(m-s))?

fn check_contradiction(r2: f64, beta: f64, m: i64) -> bool {
    // Returns true if the contradiction s > r²βk ⟹ s·m > r²(k-s)(s+β²(m-s)) holds
    // for ALL k in 1..=m and ALL integer s with s > r²βk and s < k
    let eps = r2 * beta;
    if eps >= 1.0 { return true; }
    for k in 1..=m {
        let s_min = (eps * k as f64).floor() as i64 + 1;
        for s in s_min.max(1)..k.min(m + 1) as i64 {
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
    true
}

fn main() {
    // Test: does s·m > r²·(k-s)·(s + β²·(m-s)) always hold when s > r²·β·k?
    // Also test the WEAKER claim: s·m > r²·(k-s)·(s + (r²β)²·(m-s))
    // i.e., using ε² instead of β² in the Tanner-like bound.
    //
    // The actual Tanner bound gives: s·m ≤ r²·(k-s)·(s + β²·(m-s))
    // The question is whether s > r²·β·k contradicts this.

    println!("=== Testing original claim: s > r²βk contradicts s·m ≤ r²(k-s)(s+β²(m-s)) ===");
    for r2 in [1.0_f64, 2.0, 4.0, 9.0, 100.0] {
        let mut count = 0;
        'outer: for beta_num in 1..10000 {
            let beta = beta_num as f64 / 10000.0;
            let eps = r2 * beta;
            if eps >= 1.0 { continue; }
            for m in [10, 50, 100, 500] {
                for k in 1..=m {
                    let s_min = (eps * k as f64).floor() as i64 + 1;
                    for s in s_min.max(1)..k.min(m + 1) as i64 {
                        let sf = s as f64;
                        let mf = m as f64;
                        let kf = k as f64;
                        let lhs = sf * mf;
                        let rhs = r2 * (kf - sf) * (sf + beta * beta * (mf - sf));
                        if lhs <= rhs + 1e-9 {
                            count += 1;
                            if count <= 3 {
                                println!(
                                    "  COUNTER r²={r2}: β={beta:.4}, ε={eps:.4}, m={m}, k={k}, s={s}: {lhs:.1} ≤ {rhs:.1}"
                                );
                            }
                        }
                    }
                }
            }
        }
        println!("  r²={r2}: {count} counterexamples total");
    }

    // Test with specific parameters from the actual application
    println!("\n=== Contradiction check for application parameters ===");
    // In the Seiferas application: r² ≤ 4, β = c^(2^l) < 1/4
    for m in [10, 50, 100, 500, 1000] {
        for beta_pct in [1, 5, 10, 15, 20, 24] {
            let beta = beta_pct as f64 / 100.0;
            let r2 = 4.0;
            let eps = r2 * beta;
            let ok = check_contradiction(r2, beta, m);
            println!("  r²=4, β={beta:.2}, ε={eps:.2}, m={m}: {}", if ok { "OK" } else { "FAIL" });
        }
    }

    // Find the minimum m for which the contradiction works for each β with r²=4
    println!("\n=== Minimum m for contradiction (r²=4) ===");
    for beta_pct in [1, 2, 5, 10, 15, 20, 24] {
        let beta = beta_pct as f64 / 100.0;
        let r2 = 4.0;
        let mut min_m = 0;
        for m in 1..=10000 {
            if check_contradiction(r2, beta, m as i64) {
                min_m = m;
                break;
            }
        }
        println!("  β={beta:.2}: min m = {min_m}");
    }

    // Also: what if we add hm : 0 < m as a hypothesis and
    // the condition that s is an integer > ε·k (not just barely above)?
    // The s > ε·k means s ≥ ⌊ε·k⌋ + 1 for integer s.
    // Check if ⌊ε·k⌋+1 always gives contradiction:
    println!("\n=== Check with integer s = ceil(ε·k) ===");
    for r2 in [2.0, 4.0] {
        for beta_pct in [1, 5, 10, 20] {
            let beta = beta_pct as f64 / 100.0;
            let eps = r2 * beta;
            if eps >= 1.0 { continue; }
            let mut found = false;
            for m in [10, 50, 100, 500, 1000] {
                for k in 1..=m {
                    let s = (eps * k as f64).ceil() as i64;
                    if s < 1 || s >= k.min(m+1) as i64 { continue; }
                    let sf = s as f64;
                    let mf = m as f64;
                    let kf = k as f64;
                    let lhs = sf * mf;
                    let rhs = r2 * (kf - sf) * (sf + beta * beta * (mf - sf));
                    if lhs <= rhs + 1e-9 {
                        if !found {
                            println!("  r²={r2}, β={beta:.2}: FAIL at m={m}, k={k}, s={s}: {lhs:.1} ≤ {rhs:.1}");
                            found = true;
                        }
                    }
                }
            }
            if !found {
                println!("  r²={r2}, β={beta:.2}: OK for all m,k tested");
            }
        }
    }
}
