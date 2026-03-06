#!/usr/bin/env -S cargo +nightly -Zscript
//! Validate the paper's benchmark comparison for removing clause 8.
//!
//! Seiferas (2009) Section 5 bounds sibling-native items (source 3) via a
//! benchmark comparison that uses stranger bounds at ALL tree levels — no
//! deviation bound (clause 8) needed. This test validates that proof strategy.
//!
//! For each parent bag D at (level-1, idx/2), we:
//! 1. Compute the outsider asymmetry |out_R - out_L| = |n_L - n_R|
//! 2. Decompose outsiders by source level
//! 3. Test whether per-level contributions are bounded by stranger-related quantities
//! 4. Test whether the sum matches the geometric series in cnativeCoeff
//!
//! Key measurements:
//! - Per-level outsider asymmetry vs per-level stranger-in-interval count
//! - Total outsider asymmetry vs cnativeCoeff formula
//! - The signed sum (s_lo - s_hi) + (n_L - n_R) + b%2 vs 2·cnativeCoeff·cap

use std::collections::BTreeMap;

#[derive(Clone)]
struct Params {
    a: f64,
    nu: f64,
    lambda: f64,
    eps: f64,
}

impl Params {
    fn capacity(&self, n: usize, t: usize, level: usize) -> f64 {
        n as f64 * self.nu.powi(t as i32) * self.a.powi(level as i32)
    }

    fn cnative_coeff(&self) -> f64 {
        let e2a2 = (2.0 * self.eps * self.a).powi(2);
        self.eps / 2.0
            + 2.0 * self.lambda * self.eps * self.a.powi(2) / (1.0 - e2a2)
            + 1.0 / (8.0 * self.a.powi(2) - 2.0)
    }
}

fn bag_size(n: usize, level: usize) -> usize {
    n / (1 << level)
}

/// Apply adversarial separator: sort, then introduce worst-case errors
fn apply_adversarial_separator(items: &mut Vec<usize>, eps: f64, lambda: f64) {
    items.sort();
    let m = items.len();
    if m <= 1 { return; }

    let fringe = (lambda * m as f64).floor() as usize;
    let middle_start = fringe;
    let middle_end = m.saturating_sub(fringe);
    let middle_size = middle_end.saturating_sub(middle_start);
    let half = middle_size / 2;

    let halving_errors = (eps * half as f64).floor() as usize;
    if halving_errors > 0 && half > 0 {
        for k in 0..halving_errors.min(half) {
            let left_pos = middle_start + half - 1 - k;
            let right_pos = middle_start + half + k;
            if left_pos < right_pos && right_pos < m {
                items.swap(left_pos, right_pos);
            }
        }
    }

    if fringe > 0 {
        let fringe_errors = (eps * fringe as f64).floor() as usize;
        for k in 0..fringe_errors.min(fringe).min(middle_size) {
            let fringe_pos = fringe - 1 - k;
            let middle_pos = middle_start + k;
            if fringe_pos < middle_pos {
                items.swap(fringe_pos, middle_pos);
            }
            let high_fringe_pos = middle_end + k;
            let high_middle_pos = middle_end - 1 - k;
            if high_middle_pos < high_fringe_pos && high_fringe_pos < m {
                items.swap(high_middle_pos, high_fringe_pos);
            }
        }
    }
}

struct BagTree {
    n: usize,
    max_level: usize,
    bags: BTreeMap<(usize, usize), Vec<usize>>,
    perm: Vec<usize>,
}

impl BagTree {
    fn new(n: usize) -> Self {
        assert!(n.is_power_of_two() && n >= 4);
        let max_level = n.trailing_zeros() as usize - 1;
        let mut bags = BTreeMap::new();
        let perm: Vec<usize> = (0..n).collect();
        bags.insert((0, 0), (0..n).collect());
        Self { n, max_level, bags, perm }
    }

    fn rank_in_bag(&self, bag: &[usize], i: usize) -> usize {
        bag.iter().filter(|&&j| self.perm[j] < self.perm[i]).count()
    }

    fn do_stage(&mut self, params: &Params, t: usize) {
        let mut splits: BTreeMap<(usize, usize), (Vec<usize>, Vec<usize>, Vec<usize>)> =
            BTreeMap::new();

        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }
            if (t + level) % 2 != 0 { continue; }

            let mut sorted_items = items.clone();
            apply_adversarial_separator(&mut sorted_items, params.eps, params.lambda);

            let b = sorted_items.len();
            let cap = params.capacity(self.n, t, level);
            let f = (params.lambda * cap).floor() as usize;

            if level == 0 {
                let half = b / 2;
                let to_parent: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| self.rank_in_bag(&sorted_items, i) >= 2 * (b / 2))
                    .copied().collect();
                let to_left: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| self.rank_in_bag(&sorted_items, i) < half)
                    .copied().collect();
                let to_right: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| {
                        let r = self.rank_in_bag(&sorted_items, i);
                        r >= half && r < 2 * (b / 2)
                    })
                    .copied().collect();
                splits.insert((level, idx), (to_parent, to_left, to_right));
            } else if level >= self.max_level {
                splits.insert((level, idx), (sorted_items, vec![], vec![]));
            } else {
                let h = (b / 2).saturating_sub(f);
                let to_parent: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| {
                        let r = self.rank_in_bag(&sorted_items, i);
                        r < f || r >= f + 2 * h
                    })
                    .copied().collect();
                let to_left: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| {
                        let r = self.rank_in_bag(&sorted_items, i);
                        r >= f && r < f + h
                    })
                    .copied().collect();
                let to_right: Vec<usize> = sorted_items.iter()
                    .filter(|&&i| {
                        let r = self.rank_in_bag(&sorted_items, i);
                        r >= f + h && r < f + 2 * h
                    })
                    .copied().collect();
                splits.insert((level, idx), (to_parent, to_left, to_right));
            }
        }

        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
        for level in 0..=self.max_level {
            if (t + 1 + level) % 2 != 0 { continue; }
            let num_bags = 1usize << level;
            for idx in 0..num_bags {
                let mut bag = Vec::new();
                if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * idx)) {
                    bag.extend(tp);
                }
                if let Some((tp, _, _)) = splits.get(&(level + 1, 2 * idx + 1)) {
                    bag.extend(tp);
                }
                if level > 0 {
                    if let Some((_, tl, tr)) = splits.get(&(level - 1, idx / 2)) {
                        if idx % 2 == 0 {
                            bag.extend(tl);
                        } else {
                            bag.extend(tr);
                        }
                    }
                }
                new_bags.insert((level, idx), bag);
            }
        }

        self.bags = new_bags;
    }

    /// Compute the deviation |C - b/2| for a bag at (level, idx).
    /// C = items with perm < boundary, where boundary = idx * bagSize + bagSize(level+1)
    fn bag_deviation(&self, level: usize, idx: usize) -> (i64, usize) {
        let items = match self.bags.get(&(level, idx)) {
            Some(v) => v,
            None => return (0, 0),
        };
        let b = items.len();
        if b == 0 { return (0, 0); }
        let lo = idx * bag_size(self.n, level);
        let boundary = lo + bag_size(self.n, level + 1);
        let c = items.iter().filter(|&&r| self.perm[r] < boundary).count();
        (c as i64 - (b / 2) as i64, b)
    }

    /// For bag D = bags(parent_level, parent_idx), compute the benchmark
    /// comparison quantities.
    fn analyze_benchmark_comparison(
        &self, params: &Params, t: usize,
    ) -> BenchmarkResult {
        let mut result = BenchmarkResult::default();

        for (&(parent_level, parent_idx), d_items) in &self.bags {
            if d_items.is_empty() { continue; }
            if parent_level >= self.max_level { continue; } // need children

            let b = d_items.len();
            let lo = parent_idx * bag_size(self.n, parent_level);
            let boundary = lo + bag_size(self.n, parent_level + 1);
            let hi = lo + bag_size(self.n, parent_level);

            if boundary > hi || hi > self.n { continue; }

            // 4-group decomposition of D's items
            let s_lo = d_items.iter().filter(|&&r| self.perm[r] < lo).count();
            let n_l = d_items.iter().filter(|&&r| self.perm[r] >= lo && self.perm[r] < boundary).count();
            let n_r = d_items.iter().filter(|&&r| self.perm[r] >= boundary && self.perm[r] < hi).count();
            let s_hi = d_items.iter().filter(|&&r| self.perm[r] >= hi).count();

            assert_eq!(s_lo + n_l + n_r + s_hi, b, "4-group partition check");

            let c = s_lo + n_l; // items with perm < boundary
            let deviation = (c as i64 - (b / 2) as i64).unsigned_abs() as f64;

            // Outsider counts: items NOT in D with perm in [lo, boundary) or [boundary, hi)
            let mut out_l = 0usize;
            let mut out_r = 0usize;

            // Per-level outsider decomposition
            // For each active level l', count items at l' with perm in [lo, boundary) and [boundary, hi)
            let mut per_level_left: BTreeMap<usize, usize> = BTreeMap::new();
            let mut per_level_right: BTreeMap<usize, usize> = BTreeMap::new();
            // Per-level: items with perm in [lo,hi) that are strangers at their level
            let mut per_level_stranger_in_interval: BTreeMap<usize, usize> = BTreeMap::new();
            // Per-level: total items with perm in [lo, hi)
            let mut per_level_total_in_interval: BTreeMap<usize, usize> = BTreeMap::new();

            for (&(l, i), items) in &self.bags {
                if (l, i) == (parent_level, parent_idx) { continue; }
                if items.is_empty() { continue; }

                let mut left = 0usize;
                let mut right = 0usize;
                let mut stranger_in_interval = 0usize;
                let mut total_in_interval = 0usize;

                for &r in items {
                    let p = self.perm[r];
                    if p >= lo && p < hi {
                        total_in_interval += 1;
                        // Is this item a stranger at level l in bag (l, i)?
                        let native_idx = p / bag_size(self.n, l);
                        if native_idx != i {
                            stranger_in_interval += 1;
                        }
                    }
                    if p >= lo && p < boundary {
                        left += 1;
                    } else if p >= boundary && p < hi {
                        right += 1;
                    }
                }

                out_l += left;
                out_r += right;
                *per_level_left.entry(l).or_default() += left;
                *per_level_right.entry(l).or_default() += right;
                *per_level_stranger_in_interval.entry(l).or_default() += stranger_in_interval;
                *per_level_total_in_interval.entry(l).or_default() += total_in_interval;
            }

            // Verify perm bijectivity: n_L + out_L = bag_size(level+1), n_R + out_R = bag_size(level+1)
            let child_bs = bag_size(self.n, parent_level + 1);
            assert_eq!(n_l + out_l, child_bs, "perm bijectivity left");
            assert_eq!(n_r + out_r, child_bs, "perm bijectivity right");

            // Verify: n_L - n_R = out_R - out_L
            assert_eq!(n_l as i64 - n_r as i64, out_r as i64 - out_l as i64, "native = outsider asymmetry");

            let outsider_asymmetry = (out_r as i64 - out_l as i64).unsigned_abs() as f64;

            let cap_parent = params.capacity(self.n, t, parent_level);
            let cnc = params.cnative_coeff();

            // Signed sum: s_lo - s_hi + out_R - out_L + b%2
            let signed_sum = (s_lo as i64 - s_hi as i64)
                + (out_r as i64 - out_l as i64)
                + (b % 2) as i64;
            let abs_signed_sum = signed_sum.unsigned_abs() as f64;

            // === Test F0: Full bound ===
            // |signed_sum| ≤ 2 * cnativeCoeff * cap(parent_level)
            let f0_budget = 2.0 * cnc * cap_parent;
            if f0_budget > 0.001 {
                let ratio = abs_signed_sum / f0_budget;
                if ratio > result.max_f0_ratio {
                    result.max_f0_ratio = ratio;
                    result.max_f0_detail = format!(
                        "({},{}) t={} |ss|={:.0} budget={:.1} ratio={:.4}",
                        parent_level, parent_idx, t, abs_signed_sum, f0_budget, ratio
                    );
                }
            }

            // === Test F_out: outsider asymmetry vs (2*cnc - lambda) * cap ===
            // If the proof decomposes: |signed_sum| ≤ |s_lo-s_hi| + |out_R-out_L| + b%2
            //                                       ≤ lambda*cap + |out_R-out_L| + 1
            // Then we need |out_R-out_L| ≤ (2*cnc - lambda)*cap - 1
            let f_out_budget = (2.0 * cnc - params.lambda) * cap_parent;
            if f_out_budget > 1.0 {
                let ratio = outsider_asymmetry / f_out_budget;
                if ratio > result.max_fout_ratio {
                    result.max_fout_ratio = ratio;
                }
            }

            // === Per-level analysis ===
            // For each active level, measure asymmetry and stranger-in-interval count
            let all_levels: Vec<usize> = {
                let mut v: Vec<usize> = per_level_left.keys()
                    .chain(per_level_right.keys())
                    .chain(per_level_stranger_in_interval.keys())
                    .copied().collect();
                v.sort(); v.dedup(); v
            };

            for &l in &all_levels {
                let left = *per_level_left.get(&l).unwrap_or(&0);
                let right = *per_level_right.get(&l).unwrap_or(&0);
                let asym = (right as i64 - left as i64).abs() as f64;
                let strangers = *per_level_stranger_in_interval.get(&l).unwrap_or(&0) as f64;
                let total = *per_level_total_in_interval.get(&l).unwrap_or(&0) as f64;

                // Track: is per-level asymmetry bounded by strangers at that level?
                if asym > 0.5 && strangers > 0.5 {
                    let ratio = asym / strangers;
                    if ratio > result.max_per_level_asym_over_strangers {
                        result.max_per_level_asym_over_strangers = ratio;
                        result.max_per_level_detail = format!(
                            "bag({},{}) t={} src_lev={} asym={:.0} strangers={:.0} total={:.0} ratio={:.2}",
                            parent_level, parent_idx, t, l, asym, strangers, total, ratio
                        );
                    }
                }

                // Track: asymmetry from levels where strangers = 0 (ancestor levels)
                if asym > 0.5 && strangers < 0.5 {
                    // Asymmetry from ancestor levels where items are native
                    result.ancestor_asym_cases += 1;
                    if asym > result.max_ancestor_asym {
                        result.max_ancestor_asym = asym;
                        result.max_ancestor_detail = format!(
                            "bag({},{}) t={} src_lev={} asym={:.0} total={:.0}",
                            parent_level, parent_idx, t, l, asym, total
                        );
                    }
                }
            }

            // === Test geometric series formula ===
            // Compute the paper's formula: outsider asymmetry ≈ contributions from
            // levels above D + subtree displacement
            //
            // Above D: sum over active levels l' < parent_level
            //   items at l' with perm ∈ [lo,hi) that are strangers at l'
            // Subtree: items at active levels l' > parent_level in D's subtree
            //   that are strangers at l' with perm ∈ [lo,hi)
            let mut above_strangers = 0usize;
            let mut subtree_strangers = 0usize;
            let mut same_level_strangers = 0usize;

            for &l in &all_levels {
                let s = *per_level_stranger_in_interval.get(&l).unwrap_or(&0);
                if l < parent_level {
                    above_strangers += s;
                } else if l > parent_level {
                    subtree_strangers += s;
                } else {
                    same_level_strangers += s;
                }
            }

            // Total stranger-in-interval across all levels
            let total_strangers_in_interval =
                above_strangers + subtree_strangers + same_level_strangers;

            // Track: |out_R - out_L| vs total_strangers_in_interval
            if outsider_asymmetry > 0.5 && total_strangers_in_interval > 0 {
                let ratio = outsider_asymmetry / total_strangers_in_interval as f64;
                if ratio > result.max_asym_over_total_strangers {
                    result.max_asym_over_total_strangers = ratio;
                    result.max_total_strangers_detail = format!(
                        "bag({},{}) t={} |outAsym|={:.0} above={} subtree={} same={} total={}",
                        parent_level, parent_idx, t, outsider_asymmetry,
                        above_strangers, subtree_strangers, same_level_strangers,
                        total_strangers_in_interval
                    );
                }
            }

            // Track: where do outsiders come from? (ancestor native vs strangers)
            let mut ancestor_native_in_interval = 0usize;
            for &l in &all_levels {
                let total = *per_level_total_in_interval.get(&l).unwrap_or(&0);
                let strangers = *per_level_stranger_in_interval.get(&l).unwrap_or(&0);
                ancestor_native_in_interval += total - strangers; // native items with perm ∈ [lo,hi)
            }

            // Track: outsider asymmetry breakdown
            if outsider_asymmetry > 0.5 {
                result.total_analyzed += 1;
                if ancestor_native_in_interval > 0 {
                    result.cases_with_ancestor_native += 1;
                }
            }

            // === Test the signed sum approach ===
            // Can we bound 2|C - b/2| directly?
            // 2(C - b/2) = (s_lo - s_hi) + (n_L - n_R) + b%2
            //
            // Approach: bound s_lo + s_hi from stranger bound, and
            // n_L - n_R from outsider analysis using stranger-in-interval
            let s_total = (s_lo + s_hi) as f64;
            let lam_cap = params.lambda * cap_parent;

            // s_lo + s_hi should be ≤ lambda * cap (1-stranger bound at parent level)
            if lam_cap > 0.001 {
                let ratio = s_total / lam_cap;
                if ratio > result.max_s_over_lam_cap {
                    result.max_s_over_lam_cap = ratio;
                }
            }

            // === Geometric series validation ===
            // For each ancestor level l' < parent_level, check:
            // (a) per-level outsider contribution / cap(l') — should be O(ε) for geometric decay
            // (b) per-level outsider contribution vs stranger bound λ·cap(l')
            //
            // The paper's argument: items from ancestor at level l' contribute
            // to outsider asymmetry proportionally to the *product* of error rates
            // along the path from l' to parent_level.
            for &l in &all_levels {
                if l >= parent_level { continue; } // only ancestors

                let left = *per_level_left.get(&l).unwrap_or(&0);
                let right = *per_level_right.get(&l).unwrap_or(&0);
                let asym = (right as i64 - left as i64).abs() as f64;
                let total = *per_level_total_in_interval.get(&l).unwrap_or(&0) as f64;
                let cap_l = params.capacity(self.n, t, l);
                let dist = parent_level - l; // tree distance from ancestor to D

                if asym > 0.5 && cap_l > 0.001 {
                    // Ratio: asymmetry from this ancestor / cap at ancestor level
                    let ratio = asym / cap_l;
                    if ratio > result.max_ancestor_asym_over_cap {
                        result.max_ancestor_asym_over_cap = ratio;
                        result.max_ancestor_asym_over_cap_detail = format!(
                            "bag({},{}) t={} anc_lev={} dist={} asym={:.0} total={:.0} cap={:.1} ratio={:.6}",
                            parent_level, parent_idx, t, l, dist, asym, total, cap_l, ratio
                        );
                    }

                    // Ratio: asymmetry / (λ·cap(l')) — compare to stranger bound
                    let lam_cap_l = params.lambda * cap_l;
                    if lam_cap_l > 0.001 {
                        let ratio2 = asym / lam_cap_l;
                        if ratio2 > result.max_ancestor_asym_over_lam_cap {
                            result.max_ancestor_asym_over_lam_cap = ratio2;
                            result.max_ancestor_asym_over_lam_cap_detail = format!(
                                "bag({},{}) t={} anc_lev={} dist={} asym={:.0} λ·cap={:.1} ratio={:.6}",
                                parent_level, parent_idx, t, l, dist, asym, lam_cap_l, ratio2
                            );
                        }
                    }
                }

                // Track: total items from ancestor / cap(l') — density measure
                if total > 0.5 && cap_l > 0.001 {
                    let ratio = total / cap_l;
                    if ratio > result.max_ancestor_total_over_cap {
                        result.max_ancestor_total_over_cap = ratio;
                        result.max_ancestor_total_detail = format!(
                            "bag({},{}) t={} anc_lev={} dist={} total={:.0} cap={:.1} ratio={:.6}",
                            parent_level, parent_idx, t, l, dist, total, cap_l, ratio
                        );
                    }
                }
            }

            // === Paper's benchmark comparison (Section 5) ===
            // The paper considers B = left child, C = right child, D = parent.
            // C-native items = items with perm ∈ C's range [boundary, hi).
            // At each level l', count C-native items that are strangers at l'
            // vs C-native items that are native at l'.
            //
            // Key: C-native items ABOVE D (at ancestor levels) that are in the
            // WRONG bag at their level = strangers at their level with perm ∈ C's range.
            // These are bounded by λε^(j-1) × cap(l').
            //
            // C-native items above D that are in the RIGHT bag at their level
            // (native at their level, perm ∈ C's range) = items in ancestor bags
            // that should be there. These are the "benchmark" items.
            //
            // The EXCESS above benchmark = displaced strangers.

            // Count C-native items at each ancestor level, split by stranger status
            let mut c_native_above_stranger = 0usize;
            let mut c_native_above_native = 0usize;
            let mut c_native_above_by_level: Vec<(usize, usize, usize)> = Vec::new(); // (level, stranger, native)

            for anc_dist in 1..=parent_level {
                let anc_level = parent_level - anc_dist;
                let anc_idx = parent_idx >> anc_dist;

                if let Some(anc_items) = self.bags.get(&(anc_level, anc_idx)) {
                    let mut stranger = 0usize;
                    let mut native = 0usize;
                    for &r in anc_items {
                        let p = self.perm[r];
                        if p >= boundary && p < hi {
                            // C-native item in ancestor bag
                            let item_native_idx = p / bag_size(self.n, anc_level);
                            if item_native_idx == anc_idx {
                                native += 1;
                            } else {
                                stranger += 1;
                            }
                        }
                    }
                    if stranger + native > 0 {
                        c_native_above_by_level.push((anc_level, stranger, native));
                    }
                    c_native_above_stranger += stranger;
                    c_native_above_native += native;
                }
            }

            // Similarly count B-native items at each ancestor level
            let mut b_native_above_stranger = 0usize;
            let mut b_native_above_native = 0usize;

            for anc_dist in 1..=parent_level {
                let anc_level = parent_level - anc_dist;
                let anc_idx = parent_idx >> anc_dist;

                if let Some(anc_items) = self.bags.get(&(anc_level, anc_idx)) {
                    for &r in anc_items {
                        let p = self.perm[r];
                        if p >= lo && p < boundary {
                            let item_native_idx = p / bag_size(self.n, anc_level);
                            if item_native_idx == anc_idx {
                                b_native_above_native += 1;
                            } else {
                                b_native_above_stranger += 1;
                            }
                        }
                    }
                }
            }

            // The asymmetry from above = (C-native above) - (B-native above)
            // = (c_stranger + c_native) - (b_stranger + b_native)
            let c_above = (c_native_above_stranger + c_native_above_native) as i64;
            let b_above = (b_native_above_stranger + b_native_above_native) as i64;
            let above_asym = (c_above - b_above).abs() as f64;

            // The paper says the STRANGER part bounds the total asymmetry from above
            // because native items should be symmetric (equal B-native and C-native
            // in ancestor bags by the benchmark).
            let above_stranger_total = (c_native_above_stranger + b_native_above_stranger) as f64;

            // Check: is the asymmetry from above bounded by the stranger totals?
            if above_asym > 0.5 {
                if above_stranger_total > 0.5 {
                    let ratio = above_asym / above_stranger_total;
                    if ratio > result.max_above_asym_over_strangers {
                        result.max_above_asym_over_strangers = ratio;
                        result.max_above_asym_detail = format!(
                            "bag({},{}) t={} above_asym={:.0} strangers={:.0} c_nat={} c_str={} b_nat={} b_str={} ratio={:.4}",
                            parent_level, parent_idx, t, above_asym, above_stranger_total,
                            c_native_above_native, c_native_above_stranger,
                            b_native_above_native, b_native_above_stranger, ratio
                        );
                    }
                } else {
                    // Asymmetry from above but no strangers — this would break the argument
                    result.above_asym_no_strangers += 1;
                    if above_asym > result.max_above_asym_no_strangers {
                        result.max_above_asym_no_strangers = above_asym;
                        result.above_asym_no_strangers_detail = format!(
                            "bag({},{}) t={} above_asym={:.0} c=({},{}), b=({},{})",
                            parent_level, parent_idx, t, above_asym,
                            c_native_above_native, c_native_above_stranger,
                            b_native_above_native, b_native_above_stranger
                        );
                    }
                }
            }

            // === Per-distance aggregate ===
            // For each tree distance d from D to ancestor, accumulate:
            //   asym(d) normalized by cap(parent_level)
            // Paper expects: asym from distance d ∝ (1/A^d) × cap(parent)
            // So asym(d) / cap(parent) ≈ (1/A)^d × constant
            // We track: asym(d) / (cap(parent) / A^d) = asym(d) × A^d / cap(parent)
            // This should be bounded by a small constant (independent of d).
            for &l in &all_levels {
                if l >= parent_level { continue; }
                let left = *per_level_left.get(&l).unwrap_or(&0);
                let right = *per_level_right.get(&l).unwrap_or(&0);
                let asym = (right as i64 - left as i64).abs() as f64;
                let total = *per_level_total_in_interval.get(&l).unwrap_or(&0) as f64;
                let dist = parent_level - l;

                if cap_parent > 0.001 {
                    // Expected contribution from distance d: cap(parent) / A^d
                    // But D's interval is 1/(2A)^d of ancestor's interval (factor of 2 per split)
                    // Actually, bag_size(n, parent_level+1) / bag_size(n, l) = 1 / 2^d
                    // (since bag_size halves each level)
                    let interval_fraction = 1.0 / (2.0_f64).powi(dist as i32);
                    let expected_total = cap_parent * params.a.powi(dist as i32) * interval_fraction;

                    // Track per-distance data
                    let entry = result.per_dist_data.entry(dist).or_insert((0.0, 0.0, 0));
                    entry.0 = entry.0.max(asym);
                    entry.1 = entry.1.max(total);
                    entry.2 += 1;

                    // Normalized: asym / expected_total
                    if expected_total > 0.001 && asym > 0.5 {
                        let ratio = asym / expected_total;
                        let entry2 = result.per_dist_norm.entry(dist).or_insert(0.0);
                        *entry2 = entry2.max(ratio);
                    }
                }
            }

            // === Recursive structure validation ===
            // For each ancestor level l', the "native items in ancestor bag A with
            // perm in D's range" create asymmetry. This asymmetry should be bounded
            // by the ancestor's own deviation × (D's interval / A's interval).
            //
            // Specifically: if ancestor A = (l', parent_idx >> (parent_level - l')),
            // then D's interval [lo, hi) is one of A's descendant intervals.
            // The asymmetry in D's range from A's native items ≤ |dev(A)| × 2 + rounding
            // (because A's deviation propagates to each sub-interval).
            //
            // More precisely: if A distributes items between children L/R with
            // deviation |C_A - b_A/2|, then at D's level, the asymmetry from A's
            // items is ≤ 2·|dev(A)| (telescoping through the tree).
            for &l in &all_levels {
                if l >= parent_level { continue; }

                let left = *per_level_left.get(&l).unwrap_or(&0);
                let right = *per_level_right.get(&l).unwrap_or(&0);
                let asym = (right as i64 - left as i64).abs() as f64;

                if asym < 0.5 { continue; }

                // Find the ancestor bag at level l
                let dist = parent_level - l;
                let anc_idx = parent_idx >> dist;
                let (anc_dev, anc_b) = self.bag_deviation(l, anc_idx);
                let abs_dev = anc_dev.unsigned_abs() as f64;

                // Check: asymmetry from ancestor's native items ≤ k × |dev(ancestor)|
                // for some small constant k (ideally 2).
                // Also check vs ancestor's b (bag size) for normalization.
                if abs_dev > 0.001 {
                    let ratio = asym / abs_dev;
                    if ratio > result.max_recursive_ratio {
                        result.max_recursive_ratio = ratio;
                        result.max_recursive_detail = format!(
                            "bag({},{}) t={} anc=({},{}) dist={} asym={:.0} |dev_anc|={:.0} b_anc={} ratio={:.4}",
                            parent_level, parent_idx, t, l, anc_idx, dist,
                            asym, abs_dev, anc_b, ratio
                        );
                    }
                }

                // Also: check asymmetry vs cnativeCoeff × cap(ancestor) × interval_fraction
                // This is the full recursive bound
                let cap_l = params.capacity(self.n, t, l);
                let interval_frac = 1.0 / (2.0_f64).powi(dist as i32);
                let recursive_budget = params.cnative_coeff() * cap_l * interval_frac;
                if recursive_budget > 0.001 {
                    let ratio = asym / recursive_budget;
                    if ratio > result.max_recursive_cnc_ratio {
                        result.max_recursive_cnc_ratio = ratio;
                        result.max_recursive_cnc_detail = format!(
                            "bag({},{}) t={} anc=({},{}) dist={} asym={:.0} budget={:.2} ratio={:.6}",
                            parent_level, parent_idx, t, l, anc_idx, dist,
                            asym, recursive_budget, ratio
                        );
                    }
                }
            }
        }

        result
    }

    /// Validate the subtree and above formulas term by term.
    /// For each bag C at level l (with parent D at l-1):
    /// - Subtree: at level l+(2k+1) (k=0,1,...), count (2k+2)-strangers in C's subtree bags.
    ///   Expected per-bag: λ·ε^(2k+1)·cap(l+2k+1). Total: λ·(2εA)^(2k+1)·b.
    /// - Above: at ancestor level l-(2k+1) (k=1,2,...), count items with perm in C's interval.
    ///   Paper expects: b/(2A)^(2k+1) per level (with equidistribution).
    ///   Weakened: ≤ cap(l-(2k+1)) = b/A^(2k+1) per level (just C's ancestor bag).
    fn validate_subtree_above_formulas(
        &self, params: &Params, t: usize,
    ) -> SubtreeAboveResult {
        let mut result = SubtreeAboveResult::default();

        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }
            if level == 0 { continue; } // need parent
            if level >= self.max_level { continue; }

            // C is at (level, idx). Its parent D is at (level-1, idx/2).
            // C's range: [lo_c, hi_c) where lo_c = idx * bagSize(level), hi_c = (idx+1) * bagSize(level)
            let bs_c = bag_size(self.n, level);
            let lo_c = idx * bs_c;
            let hi_c = lo_c + bs_c;
            if hi_c > self.n { continue; }

            let b = params.capacity(self.n, t, level); // capacity at C's level

            // === Subtree validation ===
            // Check ALL subtree depths d = 1, 2, 3, ...
            // At level l+d, bags in C's subtree: indices [idx*2^d, (idx+1)*2^d)
            // Items not native to C: nativeBagIdx(n, l, perm[r]) != idx
            // Stranger level: j = d+1 (since j-1 = (l+d) - l = d)
            // Expected per bag: λ·ε^d·cap(l+d) = λ·ε^d·A^d·b
            // Total: 2^d · λ·ε^d·A^d·b = λ·(2εA)^d·b
            for d in 1..=20 {
                let sub_level = level + d;
                if sub_level > self.max_level { break; }

                let bags_in_subtree = 1usize << d;
                let sub_idx_start = idx * bags_in_subtree;
                let sub_idx_end = sub_idx_start + bags_in_subtree;

                let mut total_j_strangers = 0usize;
                let mut total_items = 0usize;

                for si in sub_idx_start..sub_idx_end {
                    if let Some(sub_items) = self.bags.get(&(sub_level, si)) {
                        total_items += sub_items.len();
                        // Count (d+1)-strangers: items whose native bag at level l is not idx
                        for &r in sub_items {
                            let p = self.perm[r];
                            let native_at_c_level = p / bs_c;
                            if native_at_c_level != idx {
                                total_j_strangers += 1;
                            }
                        }
                    }
                }

                // Skip empty levels (inactive at this stage)
                if total_items == 0 { continue; }

                // Expected: λ·(2εA)^d·b
                let expected = params.lambda * (2.0 * params.eps * params.a).powi(d as i32) * b;

                if expected > 0.001 {
                    let ratio = if total_j_strangers > 0 {
                        total_j_strangers as f64 / expected
                    } else {
                        0.0
                    };
                    result.subtree_per_k.entry(d).or_insert(SubtreeKData::default())
                        .update(total_j_strangers as f64, expected, ratio, total_items);
                }
            }

            // === Above validation (weakened: per-ancestor-bag) ===
            // Active ancestor levels above D: l-3, l-5, l-7, ...
            // At ancestor level l-(2k+1) (for k ≥ 1):
            //   C's ancestor bag: index idx >> (2k+1)
            //   Items in ancestor bag with perm in C's range [lo_c, hi_c)
            //   Expected (paper with equidist): b/(2A)^(2k+1)
            //   Expected (weakened, no equidist): cap(l-(2k+1)) = b/A^(2k+1)
            let parent_level = level - 1;
            let mut ak = 1;
            loop {
                let anc_level_offset = 2 * ak + 1;
                if anc_level_offset > parent_level { break; }
                let anc_level = parent_level - anc_level_offset;
                let anc_idx = idx >> (anc_level_offset + 1); // C's ancestor at anc_level
                // Wait: idx is C's index at level `level`. C's ancestor at `anc_level` is
                // idx >> (level - anc_level) = idx >> (anc_level_offset + 1).
                let anc_shift = level - anc_level;
                let anc_idx_correct = idx >> anc_shift;

                // Count items in ancestor bag with perm in C's range
                let mut c_native_in_anc = 0usize;
                let mut anc_total = 0usize;
                if let Some(anc_items) = self.bags.get(&(anc_level, anc_idx_correct)) {
                    anc_total = anc_items.len();
                    for &r in anc_items {
                        let p = self.perm[r];
                        if p >= lo_c && p < hi_c {
                            c_native_in_anc += 1;
                        }
                    }
                }

                // Also count items with perm in C's range at ALL bags at this level
                // (to test equidistribution)
                let mut c_native_all_bags = 0usize;
                let mut total_all_bags = 0usize;
                let num_bags_at_level = 1usize << anc_level;
                for ai in 0..num_bags_at_level {
                    if let Some(ai_items) = self.bags.get(&(anc_level, ai)) {
                        total_all_bags += ai_items.len();
                        for &r in ai_items {
                            let p = self.perm[r];
                            if p >= lo_c && p < hi_c {
                                c_native_all_bags += 1;
                            }
                        }
                    }
                }

                // Expected (paper): b / (2A)^(2k+1) — with equidistribution
                let expected_paper = b / (2.0 * params.a).powi((2 * ak + 1) as i32);
                // Expected (weakened): cap(anc_level) = b / A^(2k+1) — just ancestor bag
                let expected_weak = b / params.a.powi((anc_level_offset + 1) as i32);
                // Wait, cap(anc_level) = b / A^(level - anc_level) = b / A^anc_shift
                let expected_weak2 = b / params.a.powi(anc_shift as i32);

                // Equidistribution test: items at level with perm in C's range =
                //   total_all_bags / num_bags_at_c_level
                let num_bags_c = 1usize << level;
                let expected_equidist = total_all_bags as f64 / num_bags_c as f64;

                if expected_paper > 0.001 {
                    let data = result.above_per_k.entry(ak).or_insert(AboveKData::default());

                    // Ratio: actual in ancestor bag / paper's expected
                    if c_native_in_anc > 0 {
                        let ratio = c_native_in_anc as f64 / expected_paper;
                        data.max_anc_bag_over_paper = data.max_anc_bag_over_paper.max(ratio);
                    }

                    // Ratio: actual in ALL bags / paper's expected
                    if c_native_all_bags > 0 {
                        let ratio = c_native_all_bags as f64 / expected_paper;
                        data.max_all_bags_over_paper = data.max_all_bags_over_paper.max(ratio);
                    }

                    // Ratio: actual in ancestor bag / weakened expected
                    if c_native_in_anc > 0 && expected_weak2 > 0.001 {
                        let ratio = c_native_in_anc as f64 / expected_weak2;
                        data.max_anc_bag_over_weak = data.max_anc_bag_over_weak.max(ratio);
                    }

                    // Equidistribution: actual in all bags vs total/num_c_bags
                    if expected_equidist > 0.001 && c_native_all_bags > 0 {
                        let ratio = c_native_all_bags as f64 / expected_equidist;
                        data.max_equidist_ratio = data.max_equidist_ratio.max(ratio);
                        data.min_equidist_ratio = if data.min_equidist_ratio == 0.0 {
                            ratio
                        } else {
                            data.min_equidist_ratio.min(ratio)
                        };
                    }

                    data.cases += 1;
                }

                ak += 1;
            }
        }

        result
    }

    /// Verify clause 4 (stranger bound) at every bag: stranger_count ≤ λ·cap(level)
    fn verify_clause4(&self, params: &Params, t: usize) -> BenchmarkResult {
        let mut result = BenchmarkResult::default();

        for (&(level, idx), items) in &self.bags {
            if items.is_empty() { continue; }

            // Count strangers: items whose native bag at this level is not (level, idx)
            let stranger_count = items.iter().filter(|&&r| {
                let native_idx = self.perm[r] / bag_size(self.n, level);
                native_idx != idx
            }).count();

            let cap = params.capacity(self.n, t, level);
            let lam_cap = params.lambda * cap;

            if lam_cap > 0.001 {
                let ratio = stranger_count as f64 / lam_cap;
                if ratio > result.max_stranger_over_lam_cap {
                    result.max_stranger_over_lam_cap = ratio;
                    result.max_stranger_detail = format!(
                        "({},{}) t={} strangers={} λ·cap={:.1} ratio={:.6}",
                        level, idx, t, stranger_count, lam_cap, ratio
                    );
                }
            }
        }

        result
    }
}

#[derive(Default, Clone)]
struct SubtreeKData {
    max_ratio: f64,    // max(actual / expected) across all C bags
    max_actual: f64,   // max actual strangers at this k
    max_expected: f64,  // corresponding expected
    max_items: usize,  // max total items at this subtree level
    cases: usize,
}

impl SubtreeKData {
    fn update(&mut self, actual: f64, expected: f64, ratio: f64, items: usize) {
        if ratio > self.max_ratio {
            self.max_ratio = ratio;
            self.max_actual = actual;
            self.max_expected = expected;
        }
        self.max_items = self.max_items.max(items);
        self.cases += 1;
    }
}

#[derive(Default, Clone)]
struct AboveKData {
    max_anc_bag_over_paper: f64,  // items in C's ancestor bag / paper's expected
    max_all_bags_over_paper: f64, // items in ALL bags at level / paper's expected
    max_anc_bag_over_weak: f64,   // items in C's ancestor bag / weakened expected
    max_equidist_ratio: f64,      // max(actual / equidist_expected)
    min_equidist_ratio: f64,      // min(actual / equidist_expected) — should be ≈ 1.0
    cases: usize,
}

#[derive(Default)]
struct SubtreeAboveResult {
    subtree_per_k: BTreeMap<usize, SubtreeKData>,  // k → subtree data at level l+(2k+1)
    above_per_k: BTreeMap<usize, AboveKData>,      // k → above data at ancestor level l-(2k+1)
}

#[derive(Default)]
struct BenchmarkResult {
    // F0: full signed sum vs 2*cnc*cap
    max_f0_ratio: f64,
    max_f0_detail: String,
    // F_out: outsider asymmetry vs (2*cnc - lambda)*cap
    max_fout_ratio: f64,
    // Per-level: asymmetry / strangers-in-interval
    max_per_level_asym_over_strangers: f64,
    max_per_level_detail: String,
    // Ancestor asymmetry (levels where strangers = 0)
    ancestor_asym_cases: usize,
    max_ancestor_asym: f64,
    max_ancestor_detail: String,
    // Total strangers in interval
    max_asym_over_total_strangers: f64,
    max_total_strangers_detail: String,
    // Stranger bound check
    max_s_over_lam_cap: f64,
    // Outsider breakdown
    total_analyzed: usize,
    cases_with_ancestor_native: usize,
    // Geometric series: ancestor asymmetry vs capacity
    max_ancestor_asym_over_cap: f64,
    max_ancestor_asym_over_cap_detail: String,
    max_ancestor_asym_over_lam_cap: f64,
    max_ancestor_asym_over_lam_cap_detail: String,
    max_ancestor_total_over_cap: f64,
    max_ancestor_total_detail: String,
    // Clause 4 validation: stranger count vs λ·cap at each bag
    max_stranger_over_lam_cap: f64,
    max_stranger_detail: String,
    // Per-distance aggregates: (max_asym, max_total, count) keyed by tree distance
    per_dist_data: BTreeMap<usize, (f64, f64, usize)>,
    // Per-distance normalized: max(asym / expected_total) keyed by tree distance
    per_dist_norm: BTreeMap<usize, f64>,
    // Recursive structure: ancestor native asymmetry / |ancestor deviation|
    max_recursive_ratio: f64,
    max_recursive_detail: String,
    // Recursive structure: ancestor native asymmetry / (cnc × cap(anc) × interval_frac)
    max_recursive_cnc_ratio: f64,
    max_recursive_cnc_detail: String,
    // Paper's benchmark: above-D asymmetry / above-D stranger count
    max_above_asym_over_strangers: f64,
    max_above_asym_detail: String,
    // Cases where above-D has asymmetry but no strangers
    above_asym_no_strangers: usize,
    max_above_asym_no_strangers: f64,
    above_asym_no_strangers_detail: String,
}

fn main() {
    let params = Params {
        a: 10.0,
        nu: 0.65,
        lambda: 0.01,
        eps: 0.01,
    };

    println!("=== Benchmark Comparison Validation ===");
    println!("Params: A={}, nu={}, lam={}, eps={}", params.a, params.nu, params.lambda, params.eps);
    println!("cnativeCoeff = {:.8}", params.cnative_coeff());
    println!();

    let mut g = BenchmarkResult::default();
    let mut sa = SubtreeAboveResult::default();

    for k in 3..=12 {
        let n = 1 << k;
        eprint!("n = {} (2^{}):", n, k);

        let mut tree = BagTree::new(n);

        let max_stages = 100;
        for t in 0..max_stages {
            tree.do_stage(&params, t);
            let r = tree.analyze_benchmark_comparison(&params, t + 1);

            // Validate subtree/above formulas
            let sa_r = tree.validate_subtree_above_formulas(&params, t + 1);
            for (kk, data) in &sa_r.subtree_per_k {
                let entry = sa.subtree_per_k.entry(*kk).or_insert(SubtreeKData::default());
                if data.max_ratio > entry.max_ratio {
                    entry.max_ratio = data.max_ratio;
                    entry.max_actual = data.max_actual;
                    entry.max_expected = data.max_expected;
                }
                entry.max_items = entry.max_items.max(data.max_items);
                entry.cases += data.cases;
            }
            for (kk, data) in &sa_r.above_per_k {
                let entry = sa.above_per_k.entry(*kk).or_insert(AboveKData::default());
                entry.max_anc_bag_over_paper = entry.max_anc_bag_over_paper.max(data.max_anc_bag_over_paper);
                entry.max_all_bags_over_paper = entry.max_all_bags_over_paper.max(data.max_all_bags_over_paper);
                entry.max_anc_bag_over_weak = entry.max_anc_bag_over_weak.max(data.max_anc_bag_over_weak);
                entry.max_equidist_ratio = entry.max_equidist_ratio.max(data.max_equidist_ratio);
                if data.min_equidist_ratio > 0.0 {
                    entry.min_equidist_ratio = if entry.min_equidist_ratio == 0.0 {
                        data.min_equidist_ratio
                    } else {
                        entry.min_equidist_ratio.min(data.min_equidist_ratio)
                    };
                }
                entry.cases += data.cases;
            }

            // Merge results
            if r.max_f0_ratio > g.max_f0_ratio {
                g.max_f0_ratio = r.max_f0_ratio;
                g.max_f0_detail = r.max_f0_detail;
            }
            g.max_fout_ratio = g.max_fout_ratio.max(r.max_fout_ratio);
            if r.max_per_level_asym_over_strangers > g.max_per_level_asym_over_strangers {
                g.max_per_level_asym_over_strangers = r.max_per_level_asym_over_strangers;
                g.max_per_level_detail = r.max_per_level_detail;
            }
            g.ancestor_asym_cases += r.ancestor_asym_cases;
            if r.max_ancestor_asym > g.max_ancestor_asym {
                g.max_ancestor_asym = r.max_ancestor_asym;
                g.max_ancestor_detail = r.max_ancestor_detail;
            }
            if r.max_asym_over_total_strangers > g.max_asym_over_total_strangers {
                g.max_asym_over_total_strangers = r.max_asym_over_total_strangers;
                g.max_total_strangers_detail = r.max_total_strangers_detail;
            }
            g.max_s_over_lam_cap = g.max_s_over_lam_cap.max(r.max_s_over_lam_cap);
            g.total_analyzed += r.total_analyzed;
            g.cases_with_ancestor_native += r.cases_with_ancestor_native;

            // Merge geometric series fields
            if r.max_ancestor_asym_over_cap > g.max_ancestor_asym_over_cap {
                g.max_ancestor_asym_over_cap = r.max_ancestor_asym_over_cap;
                g.max_ancestor_asym_over_cap_detail = r.max_ancestor_asym_over_cap_detail;
            }
            if r.max_ancestor_asym_over_lam_cap > g.max_ancestor_asym_over_lam_cap {
                g.max_ancestor_asym_over_lam_cap = r.max_ancestor_asym_over_lam_cap;
                g.max_ancestor_asym_over_lam_cap_detail = r.max_ancestor_asym_over_lam_cap_detail;
            }
            if r.max_ancestor_total_over_cap > g.max_ancestor_total_over_cap {
                g.max_ancestor_total_over_cap = r.max_ancestor_total_over_cap;
                g.max_ancestor_total_detail = r.max_ancestor_total_detail;
            }

            // Merge per-distance data
            for (d, (asym, total, count)) in &r.per_dist_data {
                let entry = g.per_dist_data.entry(*d).or_insert((0.0, 0.0, 0));
                entry.0 = entry.0.max(*asym);
                entry.1 = entry.1.max(*total);
                entry.2 += count;
            }
            for (d, norm) in &r.per_dist_norm {
                let entry = g.per_dist_norm.entry(*d).or_insert(0.0);
                *entry = entry.max(*norm);
            }

            // Merge benchmark comparison fields
            if r.max_above_asym_over_strangers > g.max_above_asym_over_strangers {
                g.max_above_asym_over_strangers = r.max_above_asym_over_strangers;
                g.max_above_asym_detail = r.max_above_asym_detail;
            }
            g.above_asym_no_strangers += r.above_asym_no_strangers;
            if r.max_above_asym_no_strangers > g.max_above_asym_no_strangers {
                g.max_above_asym_no_strangers = r.max_above_asym_no_strangers;
                g.above_asym_no_strangers_detail = r.above_asym_no_strangers_detail;
            }

            // Merge recursive structure fields
            if r.max_recursive_ratio > g.max_recursive_ratio {
                g.max_recursive_ratio = r.max_recursive_ratio;
                g.max_recursive_detail = r.max_recursive_detail;
            }
            if r.max_recursive_cnc_ratio > g.max_recursive_cnc_ratio {
                g.max_recursive_cnc_ratio = r.max_recursive_cnc_ratio;
                g.max_recursive_cnc_detail = r.max_recursive_cnc_detail;
            }

            // Merge clause 4 validation
            let c4 = tree.verify_clause4(&params, t + 1);
            if c4.max_stranger_over_lam_cap > g.max_stranger_over_lam_cap {
                g.max_stranger_over_lam_cap = c4.max_stranger_over_lam_cap;
                g.max_stranger_detail = c4.max_stranger_detail;
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < 2.0 {
                eprintln!(" converged at t={}", t + 1);
                break;
            }
        }
    }

    println!("=== RESULTS ===");
    println!();

    println!("--- Full bound (F0): |signed_sum| ≤ 2·cnc·cap ---");
    println!("  Max ratio: {:.6}", g.max_f0_ratio);
    println!("  Detail: {}", g.max_f0_detail);
    println!();

    println!("--- Outsider asymmetry (F_out): |out_R-out_L| ≤ (2·cnc-λ)·cap ---");
    println!("  Max ratio: {:.6}", g.max_fout_ratio);
    println!();

    println!("--- Per-level: asymmetry / strangers-in-interval ---");
    println!("  Max ratio: {:.6}", g.max_per_level_asym_over_strangers);
    println!("  Detail: {}", g.max_per_level_detail);
    println!();

    println!("--- Ancestor levels (strangers=0, items are native) ---");
    println!("  Cases with asymmetry: {}", g.ancestor_asym_cases);
    println!("  Max ancestor asymmetry: {:.0}", g.max_ancestor_asym);
    println!("  Detail: {}", g.max_ancestor_detail);
    println!();

    println!("--- Total: |out_R-out_L| / total_strangers_in_interval ---");
    println!("  Max ratio: {:.6}", g.max_asym_over_total_strangers);
    println!("  Detail: {}", g.max_total_strangers_detail);
    println!();

    println!("--- Stranger bound check: (s_lo+s_hi) / (λ·cap) ---");
    println!("  Max ratio: {:.6} (should be ≤ 1.0)", g.max_s_over_lam_cap);
    println!();

    println!("--- Outsider breakdown ---");
    println!("  Total bags analyzed: {}", g.total_analyzed);
    println!("  Cases with ancestor native items: {} ({:.1}%)",
        g.cases_with_ancestor_native,
        100.0 * g.cases_with_ancestor_native as f64 / g.total_analyzed.max(1) as f64);
    println!();

    println!("--- Geometric series: ancestor asymmetry / cap(ancestor) ---");
    println!("  Max ratio: {:.6}", g.max_ancestor_asym_over_cap);
    println!("  Detail: {}", g.max_ancestor_asym_over_cap_detail);
    println!();

    println!("--- Geometric series: ancestor asymmetry / (λ·cap(ancestor)) ---");
    println!("  Max ratio: {:.6} (should be ≤ 1.0 for direct bound)", g.max_ancestor_asym_over_lam_cap);
    println!("  Detail: {}", g.max_ancestor_asym_over_lam_cap_detail);
    println!();

    println!("--- Geometric series: ancestor items-in-interval / cap(ancestor) ---");
    println!("  Max ratio: {:.6} (density of ancestor items in D's range)", g.max_ancestor_total_over_cap);
    println!("  Detail: {}", g.max_ancestor_total_detail);
    println!();

    println!("--- Paper's benchmark: above-D asymmetry / above-D stranger count ---");
    println!("  Max ratio: {:.6} (should be ≤ 1.0 for paper's argument)", g.max_above_asym_over_strangers);
    println!("  Detail: {}", g.max_above_asym_detail);
    println!("  Cases with above-D asymmetry but 0 strangers: {} (should be 0)",
        g.above_asym_no_strangers);
    if g.above_asym_no_strangers > 0 {
        println!("  Worst no-strangers case: asym={:.0}", g.max_above_asym_no_strangers);
        println!("  Detail: {}", g.above_asym_no_strangers_detail);
    }
    println!();

    println!("--- Recursive: ancestor native asymmetry / |ancestor deviation| ---");
    println!("  Max ratio: {:.6} (should be small constant, ideally ≤ 2)", g.max_recursive_ratio);
    println!("  Detail: {}", g.max_recursive_detail);
    println!();

    println!("--- Recursive: ancestor asymmetry / (cnc·cap(anc)·interval_frac) ---");
    println!("  Max ratio: {:.6} (should be ≤ 1.0 for recursive argument)", g.max_recursive_cnc_ratio);
    println!("  Detail: {}", g.max_recursive_cnc_detail);
    println!();

    println!("--- Subtree formula: (d+1)-strangers at level l+d ---");
    println!("  d | j=d+1 | max(actual/expected) | max_actual | max_expected | max_items | cases");
    for (d, data) in &sa.subtree_per_k {
        println!("  {:1} |  j={:<2} | {:<20.6} | {:>10.1} | {:>12.1} | {:>9} | {:>5}",
            d, d+1, data.max_ratio, data.max_actual, data.max_expected, data.max_items, data.cases);
    }
    println!("  Expected: λ·(2εA)^d·b per level. All ratios should be ≤ 1.0.");
    println!();

    println!("--- Above formula: items with perm in C's range at ancestor levels ---");
    println!("  k | anc_bag/paper | all/paper | anc/weak | equidist max | equidist min | cases");
    for (kk, data) in &sa.above_per_k {
        println!("  {:1} | {:>12.4} | {:>9.4} | {:>8.4} | {:>12.4} | {:>12.4} | {:>5}",
            kk, data.max_anc_bag_over_paper, data.max_all_bags_over_paper,
            data.max_anc_bag_over_weak, data.max_equidist_ratio,
            data.min_equidist_ratio, data.cases);
    }
    println!("  Paper: b/(2A)^(2k+1) per level. Weakened: b/A^shift per level.");
    println!("  anc_bag/paper: items in C's ancestor bag vs paper's expected.");
    println!("  all/paper: items in ALL bags at level vs paper's expected.");
    println!("  equidist: should be ≈ 1.0 if items are uniformly distributed among C'-intervals.");
    println!();

    println!("--- Per-distance: ancestor contribution scaling ---");
    println!("  dist | max_asym | max_total | cases | max(asym/expected)");
    for (d, (asym, total, count)) in &g.per_dist_data {
        let norm = g.per_dist_norm.get(d).copied().unwrap_or(0.0);
        println!("    {:2} | {:8.1} | {:9.1} | {:5} | {:.6}",
            d, asym, total, count, norm);
    }
    println!("  (expected ∝ cap(parent)·(A/2)^d × interval_fraction)");
    println!();

    println!("--- Clause 4 validation: stranger_count / (λ·cap) at every bag ---");
    println!("  Max ratio: {:.6} (should be ≤ 1.0)", g.max_stranger_over_lam_cap);
    println!("  Detail: {}", g.max_stranger_detail);
    println!();

    // Summary verdict
    let pass = g.max_f0_ratio <= 1.0 + 1e-9;
    if pass {
        println!("PASS: Full bound holds (max ratio {:.6})", g.max_f0_ratio);
    } else {
        println!("FAIL: Full bound violated (max ratio {:.6})", g.max_f0_ratio);
        std::process::exit(1);
    }

    // Key diagnostic: can outsider asymmetry be bounded by stranger-in-interval?
    if g.max_per_level_asym_over_strangers <= 1.0 + 1e-9 {
        println!("GOOD: Per-level asymmetry ≤ per-level stranger-in-interval (ratio {:.4})",
            g.max_per_level_asym_over_strangers);
        println!("  → Triangle inequality per-level works for the proof!");
    } else {
        println!("NOTE: Per-level asymmetry > per-level stranger-in-interval (ratio {:.4})",
            g.max_per_level_asym_over_strangers);
        println!("  → Need to account for ancestor native items in the proof");
    }

    if g.ancestor_asym_cases > 0 {
        println!("NOTE: {} cases where ancestor native items create asymmetry (max {:.0})",
            g.ancestor_asym_cases, g.max_ancestor_asym);
        println!("  → Ancestor levels contribute asymmetry even without strangers");
        println!("  → This is the recursive structure the paper handles via geometric series");
    }

    if g.max_asym_over_total_strangers <= 1.0 + 1e-9 {
        println!("GOOD: Total outsider asymmetry ≤ total strangers-in-interval (ratio {:.4})",
            g.max_asym_over_total_strangers);
    } else {
        println!("NOTE: Total outsider asymmetry > total strangers-in-interval (ratio {:.4})",
            g.max_asym_over_total_strangers);
        println!("  → Proof needs more than just stranger-in-interval counts");
    }

    // Geometric series conclusion
    if g.max_ancestor_asym_over_lam_cap <= 1.0 + 1e-9 {
        println!("GOOD: Ancestor asymmetry ≤ λ·cap at every level (ratio {:.4})",
            g.max_ancestor_asym_over_lam_cap);
        println!("  → Direct bound: each ancestor level's outsider contribution ≤ stranger bound");
    } else {
        println!("NOTE: Ancestor asymmetry > λ·cap at some level (ratio {:.4})",
            g.max_ancestor_asym_over_lam_cap);
        println!("  → Need recursive argument; ancestor asymmetry ≤ {:.6}·cap",
            g.max_ancestor_asym_over_cap);
    }

    // Clause 4 conclusion
    if g.max_stranger_over_lam_cap <= 1.0 + 1e-9 {
        println!("GOOD: Clause 4 (stranger bound) holds at every bag (max ratio {:.4})",
            g.max_stranger_over_lam_cap);
    } else {
        println!("WARN: Clause 4 violated at some bag (max ratio {:.4})",
            g.max_stranger_over_lam_cap);
        println!("  Detail: {}", g.max_stranger_detail);
    }

    // Paper's benchmark comparison conclusion
    if g.max_above_asym_over_strangers <= 1.0 + 1e-9 && g.above_asym_no_strangers == 0 {
        println!("GOOD: Paper's benchmark argument works: above-D asymmetry ≤ above-D strangers");
        println!("  → Source 2 (items from above) bounded by stranger counts at ancestor levels!");
    } else if g.above_asym_no_strangers > 0 {
        println!("NOTE: {} cases with above-D asymmetry but 0 strangers above",
            g.above_asym_no_strangers);
        println!("  → Native items at ancestor bags create asymmetry even without strangers above D");
    }

    // Recursive structure conclusion
    if g.max_recursive_cnc_ratio <= 1.0 + 1e-9 {
        println!("GOOD: Recursive bound holds: anc asymmetry ≤ cnc·cap(anc)·(1/2^dist) (ratio {:.4})",
            g.max_recursive_cnc_ratio);
        println!("  → Each ancestor's contribution to D's outsider asymmetry decays geometrically");
        println!("  → Proof via strong induction on level is viable!");
    } else {
        println!("NOTE: Recursive bound ratio {:.4} > 1.0 (may need tighter analysis)",
            g.max_recursive_cnc_ratio);
    }
    if g.max_recursive_ratio > 0.001 {
        println!("  Ancestor asymmetry / |ancestor deviation|: max {:.4}",
            g.max_recursive_ratio);
        println!("  → Ancestor deviation propagates to D's interval with amplification ≤ {:.4}",
            g.max_recursive_ratio);
    }
}
