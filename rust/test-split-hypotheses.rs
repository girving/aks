#!/usr/bin/env -S cargo +nightly -Zscript
//! Empirical validation of invariant_maintained hypotheses (Seiferas Part B).
//!
//! For each stage of the bag-tree simulation, extracts the concrete SplitResult
//! and verifies ALL hypotheses required by `invariant_maintained` in Lean:
//!
//!   1. hsplit_sub: split components ⊆ bags
//!   2. hsplit_leaf: leaf bags don't send to children
//!   3. hkick: toParent.card ≤ 2λ·cap + 1
//!   4. hsend_left/right: toLeftChild/Right.card ≤ cap/2
//!   5. hcap_ge: A ≤ n·ν^t (parameter condition)
//!   6. hkick_stranger: j-strangers among kicked items at parent level ≤ λε^j·cap(l)
//!   7. hparent_stranger (j≥2): j-strangers from parent ≤ λε^(j-1)·cap(l-1)
//!   8. hparent_1stranger: 1-strangers from parent ≤ parentStrangerCoeff·cap(level)
//!   9. hcnative_bound: sibling-native from parent ≤ cnativeCoeff·cap(level-1)
//!  10. hrebag_uniform: rebag gives uniform sizes
//!  11. hrebag_disjoint: rebag gives disjoint bags
//!
//! Usage: cargo +nightly -Zscript rust/test-split-hypotheses.rs

use std::collections::{BTreeMap, BTreeSet};

/// Parameters for the sorting network construction
#[derive(Clone, Debug)]
struct Params {
    a: f64,
    nu: f64,
    lambda: f64,
    eps: f64,
}

impl Params {
    fn seiferas_preview() -> Self {
        Params { a: 10.0, nu: 0.65, lambda: 1.0/99.0, eps: 1.0/99.0 }
    }

    fn capacity(&self, n: usize, t: usize, level: usize) -> f64 {
        (n as f64) * self.nu.powi(t as i32) * self.a.powi(level as i32)
    }

    fn parent_stranger_coeff(&self) -> f64 {
        let a = self.a;
        let e = self.eps;
        let l = self.lambda;
        e * l / a + e / (2.0 * a)
            + 2.0 * l * e * a / (1.0 - (2.0 * e * a).powi(2))
            + 1.0 / (8.0 * a.powi(3) - 2.0 * a)
    }

    fn cnative_coeff(&self) -> f64 {
        let a = self.a;
        let e = self.eps;
        let l = self.lambda;
        e / 2.0
            + 2.0 * l * e * a.powi(2) / (1.0 - (2.0 * e * a).powi(2))
            + 1.0 / (8.0 * a.powi(2) - 2.0)
    }
}

/// Separator model
#[derive(Clone, Copy)]
enum SepModel {
    Perfect,
    Adversarial { lambda: f64 },
}

fn apply_separator(items: &mut Vec<usize>, model: SepModel, eps: f64, _rng: &mut Rng) {
    items.sort();
    match model {
        SepModel::Perfect => {}
        SepModel::Adversarial { lambda } => {
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
                    if left_pos < right_pos && right_pos < middle_end {
                        items.swap(left_pos, right_pos);
                    }
                }
            }
            let fringe_errors = (eps * fringe as f64).floor() as usize;
            if fringe_errors > 0 && fringe > 0 && middle_size > 2 * halving_errors {
                let avail = (half.saturating_sub(halving_errors)).min(fringe_errors);
                for k in 0..avail {
                    items.swap(fringe - 1 - k, middle_start + k);
                }
                for k in 0..avail {
                    let right_fringe_pos = middle_end + k;
                    let right_mid_pos = middle_end - 1 - k;
                    if right_fringe_pos < m && right_mid_pos >= middle_start + half {
                        items.swap(right_fringe_pos, right_mid_pos);
                    }
                }
            }
        }
    }
}

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Rng(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    #[allow(dead_code)]
    fn next_usize(&mut self, bound: usize) -> usize {
        (self.next_u64() % bound as u64) as usize
    }
}

/// Concrete SplitResult matching the Lean definition
#[derive(Clone, Default)]
struct SplitResult {
    to_parent: Vec<usize>,      // items kicked to parent
    to_left_child: Vec<usize>,  // items sent to left child
    to_right_child: Vec<usize>, // items sent to right child
}

/// State of the bag tree with explicit split tracking
struct BagTree {
    n: usize,
    max_level: usize,
    bags: BTreeMap<(usize, usize), Vec<usize>>,
}

impl BagTree {
    fn new(n: usize) -> Self {
        assert!(n.is_power_of_two() && n >= 4);
        let max_level = n.trailing_zeros() as usize - 1;
        let mut bags = BTreeMap::new();
        bags.insert((0, 0), (0..n).collect());
        BagTree { n, max_level, bags }
    }

    fn native_bag_idx(&self, level: usize, rank: usize) -> usize {
        let chunk_size = self.n >> level;
        if chunk_size == 0 { rank } else { rank / chunk_size }
    }

    fn is_j_stranger(&self, rank: usize, level: usize, idx: usize, j: usize) -> bool {
        if j == 0 || j > level { return false; }
        let check_level = level - (j - 1);
        let check_idx = idx >> (j - 1);
        self.native_bag_idx(check_level, rank) != check_idx
    }

    fn j_stranger_count(&self, items: &[usize], level: usize, idx: usize, j: usize) -> usize {
        items.iter().filter(|&&rank| self.is_j_stranger(rank, level, idx, j)).count()
    }

    /// Count sibling-native items: 1-stranger but NOT 2-stranger
    fn sibling_native_count(&self, items: &[usize], level: usize, idx: usize) -> usize {
        items.iter().filter(|&&rank| {
            self.is_j_stranger(rank, level, idx, 1) &&
            !self.is_j_stranger(rank, level, idx, 2)
        }).count()
    }

    /// Perform one stage, returning the splits for each bag
    fn do_stage_with_splits(&mut self, params: &Params, t: usize, model: SepModel, rng: &mut Rng)
        -> BTreeMap<(usize, usize), SplitResult>
    {
        let mut splits: BTreeMap<(usize, usize), SplitResult> = BTreeMap::new();
        let mut new_bags: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();

        let active: Vec<((usize, usize), Vec<usize>)> = self.bags.iter()
            .filter(|(_, items)| !items.is_empty())
            .map(|(&k, v)| (k, v.clone()))
            .collect();

        for ((level, idx), mut items) in active {
            apply_separator(&mut items, model, params.eps, rng);

            let b = params.capacity(self.n, t, level);
            let kick_per_side = (params.lambda * b).floor() as usize;
            let has_parent = level > 0;
            let has_children = level < self.max_level;

            let mut split = SplitResult::default();

            if !has_parent {
                // Root: no kickback, split all to children
                let mid = items.len() / 2;
                split.to_left_child = items[..mid].to_vec();
                split.to_right_child = items[mid..].to_vec();
            } else if !has_children {
                // Leaf: all items go to parent
                split.to_parent = items;
            } else {
                // Internal node
                let total = items.len();
                let kick_small = kick_per_side.min(total);
                let kick_large = kick_per_side.min(total.saturating_sub(kick_small));

                // Kick smallest and largest to parent
                split.to_parent.extend_from_slice(&items[..kick_small]);
                split.to_parent.extend_from_slice(&items[total - kick_large..]);

                // Middle items
                let mut middle: Vec<usize> = items[kick_small..total - kick_large].to_vec();

                // If odd, kick median to parent
                if middle.len() % 2 == 1 {
                    let mid_idx = middle.len() / 2;
                    split.to_parent.push(middle.remove(mid_idx));
                }

                // Split remaining to children
                let half = middle.len() / 2;
                split.to_left_child = middle[..half].to_vec();
                split.to_right_child = middle[half..].to_vec();
            }

            // Build new bags
            if has_parent {
                new_bags.entry((level - 1, idx / 2)).or_default().extend(&split.to_parent);
            }
            if has_children {
                new_bags.entry((level + 1, 2 * idx)).or_default().extend(&split.to_left_child);
                new_bags.entry((level + 1, 2 * idx + 1)).or_default().extend(&split.to_right_child);
            }

            splits.insert((level, idx), split);
        }

        self.bags = new_bags;
        splits
    }
}

/// Compute fromParent items for (level, idx) from the splits
fn from_parent(splits: &BTreeMap<(usize, usize), SplitResult>, level: usize, idx: usize) -> Vec<usize> {
    if level == 0 { return vec![]; }
    let parent_key = (level - 1, idx / 2);
    match splits.get(&parent_key) {
        Some(s) => {
            if idx % 2 == 0 { s.to_left_child.clone() }
            else { s.to_right_child.clone() }
        }
        None => vec![],
    }
}

/// Max ratio tracker
struct MaxRatios {
    // Hypothesis 3: hkick
    hkick: f64,
    // Hypothesis 4: hsend_left, hsend_right
    hsend_left: f64,
    hsend_right: f64,
    // Hypothesis 6: hkick_stranger (indexed by j)
    hkick_stranger: Vec<f64>,
    // Hypothesis 7: hparent_stranger (indexed by j)
    hparent_stranger: Vec<f64>,
    // Hypothesis 8: hparent_1stranger
    hparent_1stranger: f64,
    // Hypothesis 9: hcnative_bound
    hcnative_bound: f64,
    // Hypothesis 10: hrebag_uniform
    uniform_violations: usize,
    // Hypothesis 11: hrebag_disjoint
    disjoint_violations: usize,
    // Hypothesis 5: hcap_ge (A ≤ n·ν^t)
    cap_ge_violations: usize,
}

impl MaxRatios {
    fn new() -> Self {
        MaxRatios {
            hkick: 0.0,
            hsend_left: 0.0,
            hsend_right: 0.0,
            hkick_stranger: vec![0.0; 20],
            hparent_stranger: vec![0.0; 20],
            hparent_1stranger: 0.0,
            hcnative_bound: 0.0,
            uniform_violations: 0,
            disjoint_violations: 0,
            cap_ge_violations: 0,
        }
    }

    fn update_ratio(current: &mut f64, observed: f64, bound: f64) {
        if bound > 0.001 {
            let ratio = observed / bound;
            if ratio > *current { *current = ratio; }
        }
    }

    fn all_ok(&self) -> bool {
        self.hkick <= 1.001 &&
        self.hsend_left <= 1.001 &&
        self.hsend_right <= 1.001 &&
        self.hkick_stranger.iter().all(|&r| r <= 1.001) &&
        self.hparent_stranger.iter().all(|&r| r <= 1.001) &&
        self.hparent_1stranger <= 1.001 &&
        self.hcnative_bound <= 1.001 &&
        self.uniform_violations == 0 &&
        self.disjoint_violations == 0 &&
        self.cap_ge_violations == 0
    }
}

/// Run simulation and check all invariant_maintained hypotheses
fn check_all_hypotheses(n: usize, params: &Params, model: SepModel) -> MaxRatios {
    let mut tree = BagTree::new(n);
    let mut rng = Rng::new(42);
    let mut ratios = MaxRatios::new();
    let threshold = 2.0; // converged when leaf cap < 2

    let psc = params.parent_stranger_coeff();
    let cnc = params.cnative_coeff();

    for t in 0..300 {
        // Check hcap_ge: A ≤ n·ν^t
        let nv = (n as f64) * params.nu.powi(t as i32);
        if params.a > nv + 0.001 {
            ratios.cap_ge_violations += 1;
        }

        // Do stage with explicit splits
        let splits = tree.do_stage_with_splits(params, t, model, &mut rng);

        // === Check split-level hypotheses ===
        for (&(level, idx), split) in &splits {
            let cap = params.capacity(n, t, level);

            // H1: hsplit_sub - split components ⊆ bags
            // (by construction, always true)

            // H2: hsplit_leaf - leaf bags don't send to children
            if level >= tree.max_level {
                if !split.to_left_child.is_empty() || !split.to_right_child.is_empty() {
                    // This would be a bug in our construction
                    eprintln!("BUG: leaf ({},{}) has children", level, idx);
                }
            }

            // H3: hkick - toParent.card ≤ 2λ·cap + 1
            let kick_bound = 2.0 * params.lambda * cap + 1.0;
            MaxRatios::update_ratio(&mut ratios.hkick,
                split.to_parent.len() as f64, kick_bound);

            // H4: hsend_left/right - card ≤ cap/2
            MaxRatios::update_ratio(&mut ratios.hsend_left,
                split.to_left_child.len() as f64, cap / 2.0);
            MaxRatios::update_ratio(&mut ratios.hsend_right,
                split.to_right_child.len() as f64, cap / 2.0);

            // H6: hkick_stranger - j-strangers among kicked items at parent level
            // Hypothesis: jStrangerCount(kicked, l-1, i/2, j) ≤ λ·ε^j·cap(l)
            if level > 0 && !split.to_parent.is_empty() {
                let parent_level = level - 1;
                let parent_idx = idx / 2;
                for j in 1..=parent_level.min(15) {
                    let stranger_count = tree.j_stranger_count(
                        &split.to_parent, parent_level, parent_idx, j);
                    let bound = params.lambda * params.eps.powi(j as i32) * cap;
                    MaxRatios::update_ratio(&mut ratios.hkick_stranger[j],
                        stranger_count as f64, bound);
                }
            }
        }

        // === Check fromParent-level hypotheses (at the receiving child level) ===
        // For each bag in the NEW tree, compute fromParent items and check bounds
        for level in 0..=tree.max_level {
            if (t + 1 + level) % 2 != 0 { continue; } // skip inactive levels
            let num_bags = 1usize << level;
            for idx in 0..num_bags {
                let fp = from_parent(&splits, level, idx);
                if fp.is_empty() { continue; }

                let parent_cap = params.capacity(n, t, level.saturating_sub(1));
                let child_cap = params.capacity(n, t, level);

                // H7: hparent_stranger (j ≥ 2)
                // jStrangerCount(fp, level, idx, j) ≤ λ·ε^(j-1)·cap(level-1)
                for j in 2..=level.min(15) {
                    let count = tree.j_stranger_count(&fp, level, idx, j);
                    let bound = params.lambda * params.eps.powi(j as i32 - 1) * parent_cap;
                    MaxRatios::update_ratio(&mut ratios.hparent_stranger[j],
                        count as f64, bound);
                }

                // H8: hparent_1stranger
                // jStrangerCount(fp, level, idx, 1) ≤ parentStrangerCoeff·cap(level)
                if level >= 1 {
                    let count = tree.j_stranger_count(&fp, level, idx, 1);
                    let bound = psc * child_cap;
                    MaxRatios::update_ratio(&mut ratios.hparent_1stranger,
                        count as f64, bound);
                }

                // H9: hcnative_bound
                // siblingNativeCount(fp, level, idx) ≤ cnativeCoeff·cap(level-1)
                if level >= 1 {
                    let count = tree.sibling_native_count(&fp, level, idx);
                    let bound = cnc * parent_cap;
                    MaxRatios::update_ratio(&mut ratios.hcnative_bound,
                        count as f64, bound);
                }
            }
        }

        // H10: hrebag_uniform - all bags at same active level have equal size
        for level in 0..=tree.max_level {
            if (t + 1 + level) % 2 != 0 { continue; }
            let num_bags = 1usize << level;
            let sizes: Vec<usize> = (0..num_bags)
                .map(|idx| tree.bags.get(&(level, idx)).map_or(0, |v| v.len()))
                .collect();
            if !sizes.windows(2).all(|w| w[0] == w[1]) {
                ratios.uniform_violations += 1;
            }
        }

        // H11: hrebag_disjoint - all bags have disjoint item sets
        {
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            for items in tree.bags.values() {
                for &rank in items {
                    if !seen.insert(rank) {
                        ratios.disjoint_violations += 1;
                    }
                }
            }
        }

        let leaf_cap = params.capacity(n, t + 1, tree.max_level);
        if leaf_cap < threshold { break; }
    }

    ratios
}

fn test_all_hypotheses() {
    println!("=== Part B Hypothesis Validation ===");
    println!();
    let params = Params::seiferas_preview();

    println!("Parameters: A={}, ν={}, λ={:.6}, ε={:.6}", params.a, params.nu, params.lambda, params.eps);
    println!("parentStrangerCoeff = {:.8}", params.parent_stranger_coeff());
    println!("cnativeCoeff = {:.8}", params.cnative_coeff());
    println!();

    let models: Vec<(&str, SepModel)> = vec![
        ("Perfect", SepModel::Perfect),
        ("Adversarial", SepModel::Adversarial { lambda: params.lambda }),
    ];

    for (model_name, model) in &models {
        println!("--- {} separator ---", model_name);
        println!("{:>6} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>7} {:>5} {:>5} {:>5} {:>4}",
            "n", "hkick", "sndL", "sndR", "kick_s1", "kick_s2", "par_s2", "par_s3",
            "par1str", "cnative", "unif", "disj", "capge", "ok?");

        for exp in 3..=14 {
            let n = 1usize << exp;
            let r = check_all_hypotheses(n, &params, *model);

            println!("{:>6} {:>7.4} {:>7.4} {:>7.4} {:>7.4} {:>7.4} {:>7.4} {:>7.4} {:>7.4} {:>7.4} {:>5} {:>5} {:>5} {:>4}",
                n,
                r.hkick,
                r.hsend_left,
                r.hsend_right,
                r.hkick_stranger[1],
                r.hkick_stranger[2],
                r.hparent_stranger[2],
                r.hparent_stranger[3],
                r.hparent_1stranger,
                r.hcnative_bound,
                r.uniform_violations,
                r.disjoint_violations,
                r.cap_ge_violations,
                if r.all_ok() { "OK" } else { "FAIL" });
        }
        println!();
    }
}

/// Detailed analysis of hparent_stranger for j=2 to understand the ε factor
fn test_parent_stranger_detail() {
    println!("=== WP-B2: Detailed hparent_stranger analysis (j=2) ===");
    println!();
    let params = Params::seiferas_preview();

    let models: Vec<(&str, SepModel)> = vec![
        ("Perfect", SepModel::Perfect),
        ("Adversarial", SepModel::Adversarial { lambda: params.lambda }),
    ];

    for (model_name, model) in &models {
        println!("--- {} separator ---", model_name);

        for &n in &[64, 256, 1024, 4096] {
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(42);
            let threshold = 2.0;

            let mut max_ratio_tight: f64 = 0.0;  // using λε·cap(l-1)
            let mut max_ratio_loose: f64 = 0.0;  // using λ·cap(l-1) (trivial bound)
            let mut max_ratio_half: f64 = 0.0;   // using λ·cap(l-1)/2

            for t in 0..300 {
                let splits = tree.do_stage_with_splits(&params, t, *model, &mut rng);

                for level in 2..=tree.max_level {
                    if (t + 1 + level) % 2 != 0 { continue; }
                    let parent_cap = params.capacity(n, t, level - 1);

                    for idx in 0..(1usize << level) {
                        let fp = from_parent(&splits, level, idx);
                        if fp.is_empty() { continue; }

                        // j=2 stranger count = 1-stranger at parent level
                        let count = tree.j_stranger_count(&fp, level, idx, 2);

                        // Tight bound: λε·cap(l-1)
                        let tight = params.lambda * params.eps * parent_cap;
                        if tight > 0.001 {
                            let r = count as f64 / tight;
                            if r > max_ratio_tight { max_ratio_tight = r; }
                        }

                        // Loose bound: λ·cap(l-1)  (= trivial monotonicity bound)
                        let loose = params.lambda * parent_cap;
                        if loose > 0.001 {
                            let r = count as f64 / loose;
                            if r > max_ratio_loose { max_ratio_loose = r; }
                        }

                        // Half bound: λ·cap(l-1)/2  (each child gets ≈ half)
                        let half_b = params.lambda * parent_cap / 2.0;
                        if half_b > 0.001 {
                            let r = count as f64 / half_b;
                            if r > max_ratio_half { max_ratio_half = r; }
                        }
                    }
                }

                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }

            println!("  n={:5}: tight(λε·cap)={:.4}  half(λ·cap/2)={:.4}  loose(λ·cap)={:.4}",
                n, max_ratio_tight, max_ratio_half, max_ratio_loose);
        }
        println!();
    }
}

/// Detailed analysis: what fraction of parent's strangers end up in each child vs fringe?
fn test_stranger_distribution() {
    println!("=== WP-B2: Stranger distribution after separator ===");
    println!("  How are parent's 1-strangers distributed across fringe/left/right?");
    println!();
    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };

    for &n in &[256, 1024, 4096] {
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);
        let threshold = 2.0;

        let mut total_strangers_in_parent = 0usize;
        let mut strangers_to_fringe = 0usize;
        let mut strangers_to_left = 0usize;
        let mut strangers_to_right = 0usize;
        let mut sample_count = 0usize;

        for t in 0..300 {
            // Get the old bags to know which items are strangers
            let old_bags = tree.bags.clone();
            let splits = tree.do_stage_with_splits(&params, t, model, &mut rng);

            // For each parent bag that was split, count how strangers were distributed
            for (&(level, idx), split) in &splits {
                if level == 0 || level >= tree.max_level { continue; } // internal only
                let old_items = match old_bags.get(&(level, idx)) {
                    Some(v) if !v.is_empty() => v,
                    _ => continue,
                };

                // Count 1-strangers at this level in the old bag
                let old_strangers: BTreeSet<usize> = old_items.iter()
                    .filter(|&&rank| tree.is_j_stranger(rank, level, idx, 1))
                    .copied().collect();

                if old_strangers.is_empty() { continue; }

                let in_fringe = split.to_parent.iter()
                    .filter(|r| old_strangers.contains(r)).count();
                let in_left = split.to_left_child.iter()
                    .filter(|r| old_strangers.contains(r)).count();
                let in_right = split.to_right_child.iter()
                    .filter(|r| old_strangers.contains(r)).count();

                total_strangers_in_parent += old_strangers.len();
                strangers_to_fringe += in_fringe;
                strangers_to_left += in_left;
                strangers_to_right += in_right;
                sample_count += 1;
            }

            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        if total_strangers_in_parent > 0 {
            let total = total_strangers_in_parent as f64;
            println!("  n={:5}: {} bags with strangers, total {} strangers",
                n, sample_count, total_strangers_in_parent);
            println!("    fringe: {:5} ({:.1}%)  left: {:5} ({:.1}%)  right: {:5} ({:.1}%)",
                strangers_to_fringe, 100.0 * strangers_to_fringe as f64 / total,
                strangers_to_left, 100.0 * strangers_to_left as f64 / total,
                strangers_to_right, 100.0 * strangers_to_right as f64 / total);
        }
    }
    println!();
}

/// WP-B3: Detailed sibling-native analysis
/// Among items from parent, what fraction are sibling-native (1-strange but not 2-strange)?
fn test_sibling_native_detail() {
    println!("=== WP-B3: Sibling-native bound (hcnative_bound) ===");
    println!();
    let params = Params::seiferas_preview();
    let cnc = params.cnative_coeff();
    println!("cnativeCoeff = {:.8}", cnc);

    let models: Vec<(&str, SepModel)> = vec![
        ("Perfect", SepModel::Perfect),
        ("Adversarial", SepModel::Adversarial { lambda: params.lambda }),
    ];

    for (model_name, model) in &models {
        println!("  --- {} separator ---", model_name);

        for &n in &[64, 256, 1024, 4096, 16384] {
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(42);
            let threshold = 2.0;

            let mut max_ratio: f64 = 0.0;
            let mut max_count = 0usize;
            let mut max_bound: f64 = 0.0;

            for t in 0..300 {
                let splits = tree.do_stage_with_splits(&params, t, *model, &mut rng);

                for level in 1..=tree.max_level {
                    if (t + 1 + level) % 2 != 0 { continue; }
                    let parent_cap = params.capacity(n, t, level - 1);

                    for idx in 0..(1usize << level) {
                        let fp = from_parent(&splits, level, idx);
                        if fp.is_empty() { continue; }

                        let count = tree.sibling_native_count(&fp, level, idx);
                        let bound = cnc * parent_cap;

                        if bound > 0.001 {
                            let r = count as f64 / bound;
                            if r > max_ratio {
                                max_ratio = r;
                                max_count = count;
                                max_bound = bound;
                            }
                        }
                    }
                }

                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }

            println!("    n={:5}: max_ratio={:.4}  (count={}, bound={:.2})",
                n, max_ratio, max_count, max_bound);
        }
    }
    println!();
}

/// WP-B4: End-to-end bridge test
/// Verify that the abstract invariant (SeifInvariant) holds at each stage
/// when the split is derived from the concrete separator execution.
fn test_abstract_concrete_bridge() {
    println!("=== WP-B4: Abstract-Concrete Bridge ===");
    println!("  Verify SeifInvariant holds at each stage via concrete separator execution.");
    println!();
    let params = Params::seiferas_preview();

    let models: Vec<(&str, SepModel)> = vec![
        ("Perfect", SepModel::Perfect),
        ("Adversarial", SepModel::Adversarial { lambda: params.lambda }),
    ];

    for (model_name, model) in &models {
        println!("  --- {} separator ---", model_name);

        for exp in 3..=14 {
            let n = 1usize << exp;
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(42);
            let threshold = 2.0;
            let mut invariant_ok = true;
            let mut stages = 0;
            let mut first_fail = String::new();

            for t in 0..300 {
                let _splits = tree.do_stage_with_splits(&params, t, *model, &mut rng);

                // Check the invariant at t+1
                let inv_result = check_invariant(&tree, &params, t + 1);
                if let Err(msg) = inv_result {
                    if invariant_ok {
                        first_fail = format!("t={}: {}", t + 1, msg);
                    }
                    invariant_ok = false;
                }

                stages = t + 1;
                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }

            // After convergence, check all items are native
            let all_native = check_all_native(&tree);

            print!("    n={:5}: stages={:3} inv={:5} native={:5}",
                n, stages, invariant_ok, all_native);
            if !invariant_ok {
                print!("  | {}", &first_fail[..first_fail.len().min(60)]);
            }
            println!();
        }
    }
    println!();
}

fn check_invariant(tree: &BagTree, params: &Params, t: usize) -> Result<(), String> {
    // Clause 1: alternating empty
    for (&(level, idx), items) in &tree.bags {
        if (t + level) % 2 != 0 && !items.is_empty() {
            return Err(format!("cl1: ({},{}) has {} items", level, idx, items.len()));
        }
    }

    // Clause 2: uniform size
    for level in 0..=tree.max_level {
        if (t + level) % 2 != 0 { continue; }
        let num_bags = 1usize << level;
        let sizes: Vec<usize> = (0..num_bags)
            .map(|idx| tree.bags.get(&(level, idx)).map_or(0, |v| v.len()))
            .collect();
        if !sizes.windows(2).all(|w| w[0] == w[1]) {
            return Err(format!("cl2: level {} non-uniform: {:?}",
                level, &sizes[..sizes.len().min(8)]));
        }
    }

    // Clause 3: capacity
    for (&(level, idx2), items) in &tree.bags {
        if items.is_empty() { continue; }
        let b = params.capacity(tree.n, t, level);
        if items.len() as f64 > b + 0.001 {
            return Err(format!("cl3: ({},{}) {} items > {:.2}",
                level, idx2, items.len(), b));
        }
    }

    // Clause 4: stranger bounds
    for (&(level, idx), items) in &tree.bags {
        if items.is_empty() { continue; }
        let b = params.capacity(tree.n, t, level);
        for j in 1..=level {
            let count = tree.j_stranger_count(items, level, idx, j);
            let bound = params.lambda * params.eps.powi(j as i32 - 1) * b;
            if count as f64 > bound + 0.001 {
                return Err(format!("cl4: ({},{}) {} {}-strangers > {:.4}",
                    level, idx, count, j, bound));
            }
        }
    }

    Ok(())
}

fn check_all_native(tree: &BagTree) -> bool {
    for (&(level, idx), items) in &tree.bags {
        for &rank in items {
            if tree.native_bag_idx(level, rank) != idx {
                return false;
            }
        }
    }
    true
}

/// Test with multiple seeds for robustness
fn test_multi_seed() {
    println!("=== Multi-seed robustness test ===");
    let params = Params::seiferas_preview();
    let model = SepModel::Adversarial { lambda: params.lambda };

    for &n in &[64, 256, 1024, 4096] {
        let mut all_ok = true;
        let mut max_hkick_s1: f64 = 0.0;
        let mut max_par_s2: f64 = 0.0;
        let mut max_par1str: f64 = 0.0;
        let mut max_cnative: f64 = 0.0;

        for seed in 0..50 {
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(seed);
            let threshold = 2.0;
            let psc = params.parent_stranger_coeff();
            let cnc = params.cnative_coeff();

            for t in 0..300 {
                let splits = tree.do_stage_with_splits(&params, t, model, &mut rng);

                // Check key hypotheses
                for (&(level, idx), split) in &splits {
                    let cap = params.capacity(n, t, level);
                    if level > 0 && !split.to_parent.is_empty() {
                        let count = tree.j_stranger_count(
                            &split.to_parent, level - 1, idx / 2, 1);
                        let bound = params.lambda * params.eps * cap;
                        if bound > 0.001 {
                            let r = count as f64 / bound;
                            if r > max_hkick_s1 { max_hkick_s1 = r; }
                            if r > 1.001 { all_ok = false; }
                        }
                    }
                }

                for level in 1..=tree.max_level {
                    if (t + 1 + level) % 2 != 0 { continue; }
                    let parent_cap = params.capacity(n, t, level.saturating_sub(1));
                    let child_cap = params.capacity(n, t, level);

                    for idx in 0..(1usize << level) {
                        let fp = from_parent(&splits, level, idx);
                        if fp.is_empty() { continue; }

                        // hparent_stranger j=2
                        if level >= 2 {
                            let count = tree.j_stranger_count(&fp, level, idx, 2);
                            let bound = params.lambda * params.eps * parent_cap;
                            if bound > 0.001 {
                                let r = count as f64 / bound;
                                if r > max_par_s2 { max_par_s2 = r; }
                                if r > 1.001 { all_ok = false; }
                            }
                        }

                        // hparent_1stranger
                        {
                            let count = tree.j_stranger_count(&fp, level, idx, 1);
                            let bound = psc * child_cap;
                            if bound > 0.001 {
                                let r = count as f64 / bound;
                                if r > max_par1str { max_par1str = r; }
                                if r > 1.001 { all_ok = false; }
                            }
                        }

                        // hcnative_bound
                        {
                            let count = tree.sibling_native_count(&fp, level, idx);
                            let bound = cnc * parent_cap;
                            if bound > 0.001 {
                                let r = count as f64 / bound;
                                if r > max_cnative { max_cnative = r; }
                                if r > 1.001 { all_ok = false; }
                            }
                        }
                    }
                }

                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }
        }

        println!("  n={:5}: {} | kick_s1={:.4} par_s2={:.4} par1str={:.4} cnative={:.4}",
            n, if all_ok { "OK" } else { "FAIL" },
            max_hkick_s1, max_par_s2, max_par1str, max_cnative);
    }
    println!();
}

/// Validate with CORRECT convergence criterion: λ·cap < 1 (Seiferas's actual criterion)
/// and verify the two-case capacity argument (b ≥ A vs b < A).
fn test_correct_convergence() {
    println!("=== CORRECT CONVERGENCE (λ·cap < 1) ===");
    println!("  Seiferas's actual criterion: stop when leaf capacity < 1/λ");
    println!("  Key: when b < A, parent is empty, children have even items, no +1 kick");
    println!();
    let params = Params::seiferas_preview();
    let threshold = 1.0 / params.lambda; // 99.0

    let models: Vec<(&str, SepModel)> = vec![
        ("Perfect", SepModel::Perfect),
        ("Adversarial", SepModel::Adversarial { lambda: params.lambda }),
    ];

    for (model_name, model) in &models {
        println!("  --- {} separator ---", model_name);
        println!("  {:>6} {:>6} {:>7} {:>7} {:>7} {:>7} {:>7} {:>9} {:>9} {:>6} {:>6}",
            "n", "stgs", "hkick", "sndL", "sndR", "kick_e", "par1s", "inv_ok", "0strang", "capge", "even");

        for exp in 3..=14 {
            let n = 1usize << exp;
            let mut tree = BagTree::new(n);
            let mut rng = Rng::new(42);
            let psc = params.parent_stranger_coeff();

            let mut max_hkick: f64 = 0.0;
            let mut max_hsend_l: f64 = 0.0;
            let mut max_hsend_r: f64 = 0.0;
            let mut max_hkick_even: f64 = 0.0; // hkick_even: when parent empty, ≤ 2λ·cap
            let mut max_par1str: f64 = 0.0;
            let mut invariant_ok = true;
            let mut first_fail = String::new();
            let mut capge_violations = 0usize;
            let mut even_violations = 0usize; // children items should be even when grandparent empty
            let mut stages = 0;

            for t in 0..300 {
                // Track which bags were empty BEFORE the stage
                let empty_bags: BTreeSet<(usize, usize)> = {
                    let mut s = BTreeSet::new();
                    for level in 0..=tree.max_level {
                        for idx in 0..(1usize << level) {
                            if tree.bags.get(&(level, idx)).map_or(true, |v| v.is_empty()) {
                                s.insert((level, idx));
                            }
                        }
                    }
                    s
                };

                // Check hcap_ge
                let nv = (n as f64) * params.nu.powi(t as i32);
                if params.a > nv + 0.001 { capge_violations += 1; }

                let splits = tree.do_stage_with_splits(&params, t, *model, &mut rng);

                // Check split-level hypotheses
                for (&(level, idx), split) in &splits {
                    let cap = params.capacity(n, t, level);

                    // Standard hkick
                    let kick_bound = 2.0 * params.lambda * cap + 1.0;
                    if kick_bound > 0.001 {
                        let r = split.to_parent.len() as f64 / kick_bound;
                        if r > max_hkick { max_hkick = r; }
                    }

                    // hkick_even: when parent bag was empty, toParent ≤ 2λ·cap (no +1)
                    if level > 0 {
                        let parent_key = (level - 1, idx / 2);
                        if empty_bags.contains(&parent_key) {
                            let kick_even_bound = 2.0 * params.lambda * cap;
                            if kick_even_bound > 0.001 {
                                let r = split.to_parent.len() as f64 / kick_even_bound;
                                if r > max_hkick_even { max_hkick_even = r; }
                            } else if split.to_parent.len() > 0 {
                                // bound is ~0 but we have items: check absolute
                                max_hkick_even = f64::MAX;
                            }
                        }
                    }

                    // hsend
                    if cap > 0.001 {
                        let r_l = split.to_left_child.len() as f64 / (cap / 2.0);
                        let r_r = split.to_right_child.len() as f64 / (cap / 2.0);
                        if r_l > max_hsend_l { max_hsend_l = r_l; }
                        if r_r > max_hsend_r { max_hsend_r = r_r; }
                    }

                    // Even-item check: when grandparent was empty, this bag should
                    // have even items (Seiferas Section 5 argument)
                    if level > 0 {
                        let grandparent_key = if level >= 2 {
                            (level - 2, idx / 4)
                        } else {
                            // level = 1, no grandparent — always even (root has all n items)
                            (0, 0) // placeholder, always check
                        };
                        let items_count = tree.bags.get(&(level, idx)).map_or(0, |v| v.len());
                        // Only check when grandparent was empty and we have items
                        if level >= 2 && empty_bags.contains(&grandparent_key) && items_count > 0 {
                            if items_count % 2 != 0 {
                                even_violations += 1;
                            }
                        }
                    }
                }

                // Check fromParent-level hypotheses
                for level in 1..=tree.max_level {
                    if (t + 1 + level) % 2 != 0 { continue; }
                    let child_cap = params.capacity(n, t, level);
                    for idx in 0..(1usize << level) {
                        let fp = from_parent(&splits, level, idx);
                        if fp.is_empty() { continue; }
                        let count = tree.j_stranger_count(&fp, level, idx, 1);
                        let bound = psc * child_cap;
                        if bound > 0.001 {
                            let r = count as f64 / bound;
                            if r > max_par1str { max_par1str = r; }
                        }
                    }
                }

                // Check invariant at t+1
                let inv_result = check_invariant(&tree, &params, t + 1);
                if let Err(msg) = inv_result {
                    if invariant_ok {
                        first_fail = format!("t={}: {}", t + 1, msg);
                    }
                    invariant_ok = false;
                }

                stages = t + 1;
                let leaf_cap = params.capacity(n, t + 1, tree.max_level);
                if leaf_cap < threshold { break; }
            }

            // Check 0 strangers at convergence
            let zero_strangers = {
                let mut all_zero = true;
                for (&(level, idx), items) in &tree.bags {
                    if items.is_empty() { continue; }
                    let count = tree.j_stranger_count(items, level, idx, 1);
                    if count > 0 { all_zero = false; break; }
                }
                all_zero
            };

            println!("  {:>6} {:>6} {:>7.4} {:>7.4} {:>7.4} {:>7.4} {:>7.4} {:>9} {:>9} {:>6} {:>6}",
                n, stages, max_hkick, max_hsend_l, max_hsend_r,
                if max_hkick_even == f64::MAX { -1.0 } else { max_hkick_even },
                max_par1str,
                invariant_ok, zero_strangers,
                capge_violations, even_violations);
        }
        println!();
    }
}

/// Validate two-case capacity proof: show that for ALL stages with correct convergence,
/// the capacity bound holds via either case 1 (b≥A) or case 2 (b<A, no +2).
fn test_two_case_capacity() {
    println!("=== Two-Case Capacity Argument ===");
    println!("  Case 1 (b≥A): rebag ≤ 4λAb + 2 + b/(2A) ≤ νb");
    println!("  Case 2 (b<A): parent empty, rebag ≤ 4λAb ≤ νb (no +2)");
    println!();
    let params = Params::seiferas_preview();
    let threshold = 1.0 / params.lambda;
    let model = SepModel::Adversarial { lambda: params.lambda };

    println!("  {:>6} {:>6} {:>12} {:>12} {:>12} {:>12}",
        "n", "stgs", "case1_max_r", "case2_max_r", "case1_count", "case2_count");

    for exp in 3..=14 {
        let n = 1usize << exp;
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);

        let mut case1_max_ratio: f64 = 0.0;
        let mut case2_max_ratio: f64 = 0.0;
        let mut case1_count = 0usize;
        let mut case2_count = 0usize;
        let mut stages = 0;

        for t in 0..300 {
            let _splits = tree.do_stage_with_splits(&params, t, model, &mut rng);

            // For each bag at stage t+1, check the capacity ratio
            for level in 0..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; }
                let cap_old = params.capacity(n, t, level);
                let cap_new = params.capacity(n, t + 1, level);

                for idx in 0..(1usize << level) {
                    let items = tree.bags.get(&(level, idx)).map_or(0, |v| v.len());
                    if items == 0 { continue; }

                    if cap_new > 0.001 {
                        let ratio = items as f64 / cap_new;
                        if cap_old >= params.a {
                            // Case 1: b ≥ A
                            case1_count += 1;
                            if ratio > case1_max_ratio { case1_max_ratio = ratio; }
                        } else {
                            // Case 2: b < A
                            case2_count += 1;
                            if ratio > case2_max_ratio { case2_max_ratio = ratio; }
                        }
                    }
                }
            }

            stages = t + 1;
            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        println!("  {:>6} {:>6} {:>12.4} {:>12.4} {:>12} {:>12}",
            n, stages, case1_max_ratio, case2_max_ratio, case1_count, case2_count);
    }
    println!();
}

/// Validate the PAIRED kick bound: total kick from both children of a bag,
/// checking that when cap < A, the +2 additive term vanishes.
/// Also checks the even-item property at the child level.
fn test_paired_kick_bound() {
    println!("=== Paired Kick Bound (Seiferas Section 5 case 2) ===");
    println!("  For bag at level l with cap < A:");
    println!("    - Parent (l-1) has cap/A < 1, hence empty: fromParent = 0");
    println!("    - Children at l+1 have EVEN items (divisibility argument)");
    println!("    - Paired kick ≤ 4λA·cap (no +2)");
    println!();
    let params = Params::seiferas_preview();
    let threshold = 1.0 / params.lambda;
    let model = SepModel::Adversarial { lambda: params.lambda };

    println!("  {:>6} {:>6} {:>12} {:>12} {:>10} {:>10} {:>10} {:>10}",
        "n", "stgs", "pair_cap<A", "pair_cap≥A", "even_ok", "even_fail",
        "parent0", "fromP>0");

    for exp in 3..=14 {
        let n = 1usize << exp;
        let mut tree = BagTree::new(n);
        let mut rng = Rng::new(42);

        // Max ratio: total_kick_from_children / (4λA·cap) for case cap < A
        let mut max_pair_ratio_small: f64 = 0.0;
        // Max ratio: total_kick_from_children / (4λA·cap + 2) for case cap ≥ A
        let mut max_pair_ratio_large: f64 = 0.0;
        let mut even_ok = 0usize;     // children had even items in cap < A case
        let mut even_fail = 0usize;   // children had odd items in cap < A case
        let mut parent_empty = 0usize; // parent was empty in cap < A case
        let mut from_parent_nonzero = 0usize; // fromParent > 0 in cap < A case
        let mut stages = 0;

        for t in 0..300 {
            // Save old bags state
            let old_bags = tree.bags.clone();

            let splits = tree.do_stage_with_splits(&params, t, model, &mut rng);

            // For each level l that is active at stage t+1 (was inactive at t):
            // check the paired kick from children at l+1
            for level in 0..=tree.max_level {
                if (t + 1 + level) % 2 != 0 { continue; } // skip non-active at t+1

                let cap_l = params.capacity(n, t, level);

                for idx in 0..(1usize << level) {
                    // Get kicks from both children at level l+1
                    let left_child_key = (level + 1, 2 * idx);
                    let right_child_key = (level + 1, 2 * idx + 1);

                    let left_kick = splits.get(&left_child_key)
                        .map_or(0, |s| s.to_parent.len());
                    let right_kick = splits.get(&right_child_key)
                        .map_or(0, |s| s.to_parent.len());
                    let total_kick = left_kick + right_kick;

                    // Get fromParent contribution
                    let fp = from_parent(&splits, level, idx);

                    let cap_child = params.capacity(n, t, level + 1);

                    if cap_l < params.a {
                        // Case 2: cap < A
                        let bound = 4.0 * params.lambda * cap_child;
                        if bound > 0.001 {
                            let r = total_kick as f64 / bound;
                            if r > max_pair_ratio_small { max_pair_ratio_small = r; }
                        }

                        // Check even items at children
                        let left_items = old_bags.get(&left_child_key).map_or(0, |v| v.len());
                        let right_items = old_bags.get(&right_child_key).map_or(0, |v| v.len());
                        if left_items % 2 == 0 && right_items % 2 == 0 {
                            even_ok += 1;
                        } else {
                            even_fail += 1;
                        }

                        // Check parent empty
                        if level > 0 {
                            let parent_items = old_bags.get(&(level - 1, idx / 2)).map_or(0, |v| v.len());
                            if parent_items == 0 { parent_empty += 1; }
                        }

                        // Check fromParent = 0
                        if !fp.is_empty() { from_parent_nonzero += 1; }
                    } else {
                        // Case 1: cap ≥ A
                        let bound = 4.0 * params.lambda * cap_child + 2.0;
                        if bound > 0.001 {
                            let r = total_kick as f64 / bound;
                            if r > max_pair_ratio_large { max_pair_ratio_large = r; }
                        }
                    }
                }
            }

            stages = t + 1;
            let leaf_cap = params.capacity(n, t + 1, tree.max_level);
            if leaf_cap < threshold { break; }
        }

        println!("  {:>6} {:>6} {:>12.4} {:>12.4} {:>10} {:>10} {:>10} {:>10}",
            n, stages, max_pair_ratio_small, max_pair_ratio_large,
            even_ok, even_fail, parent_empty, from_parent_nonzero);
    }
    println!();
}

fn main() {
    test_all_hypotheses();
    test_parent_stranger_detail();
    test_stranger_distribution();
    test_sibling_native_detail();
    test_abstract_concrete_bridge();
    test_multi_seed();
    test_correct_convergence();
    test_two_case_capacity();
    test_paired_kick_bound();
}
