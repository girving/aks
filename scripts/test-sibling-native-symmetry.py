#!/usr/bin/env python3
"""Test whether sibling-native counts in kicks are equal: SL = SR?

For the kick_native_deviation_bound proof, we need:
  |nLkL - nRkL + nLkR - nRkR| ≤ 2·lam·ε·cap

My analysis shows this equals (XR - XL) + 2(SR - SL) where:
- XL, XR = 1-strangers at parent level in kL, kR (bounded by kick_stranger_bound)
- SL = sibling-native items in kL (contribute to nRkL)
- SR = sibling-native items in kR (contribute to nLkR)

If SL = SR, the imbalance simplifies to XR - XL, bounded by 2·lam·ε·cap.
This test checks empirically whether SL ≈ SR.
"""

import math

A = 10.0
NU = 0.65
LAM = 0.01
EPS = 0.01

def max_level(n: int) -> int:
    if n <= 1:
        return 0
    return int(math.log2(n))

def bag_size(n: int, level: int) -> int:
    if (1 << level) > n:
        return 0
    return n // (1 << level)

def bag_capacity(n: int, t: int, level: int) -> float:
    return n * (NU ** t) * (A ** level)

def fringe_size(cap: float) -> int:
    return max(0, int(LAM * cap))

def child_send_size(b: int, cap: float) -> int:
    f = fringe_size(cap)
    if f > b // 2:
        return 0
    return b // 2 - f

def is_sibling_native(n: int, perm_val: int, level: int, idx: int) -> bool:
    """Check if item is a 1-stranger at (level, idx) but NOT a 2-stranger."""
    bs = bag_size(n, level)
    if bs == 0:
        return False

    native_idx = perm_val // bs
    is_1_stranger = native_idx != idx

    if level >= 1:
        bs_parent = bag_size(n, level - 1)
        if bs_parent == 0:
            is_2_stranger = False
        else:
            native_parent_idx = perm_val // bs_parent
            is_2_stranger = native_parent_idx != idx // 2
    else:
        is_2_stranger = False

    return is_1_stranger and not is_2_stranger

def is_parent_stranger(n: int, perm_val: int, level: int, idx: int) -> bool:
    """Check if item is a 1-stranger at parent level (level, idx)."""
    bs = bag_size(n, level)
    if bs == 0:
        return False
    native_idx = perm_val // bs
    return native_idx != idx

def rank_in_bag(perm: list, bag: set, item: int) -> int:
    return sum(1 for j in bag if perm[j] < perm[item])

def split_bag(perm: list, bag: set, n: int, cap: float, level: int):
    """Split a bag into (to_parent, to_left, to_right)."""
    b = len(bag)
    ml = max_level(n)

    if ml <= level:
        return (set(bag), set(), set())

    if level == 0:
        half = b // 2
        to_parent, to_left, to_right = set(), set(), set()
        for item in bag:
            r = rank_in_bag(perm, bag, item)
            if r < half:
                to_left.add(item)
            elif r < 2 * half:
                to_right.add(item)
            else:
                to_parent.add(item)
        return (to_parent, to_left, to_right)

    f = fringe_size(cap)
    h = child_send_size(b, cap)
    to_parent, to_left, to_right = set(), set(), set()
    for item in bag:
        r = rank_in_bag(perm, bag, item)
        if r < f or r >= f + 2 * h:
            to_parent.add(item)
        elif r < f + h:
            to_left.add(item)
        else:
            to_right.add(item)
    return (to_parent, to_left, to_right)

class BagAssignment:
    def __init__(self, n: int):
        self.n = n
        ml = max_level(n)
        self.bags = []
        for level in range(ml + 2):
            count = min(1 << level, n)
            self.bags.append([set() for _ in range(count)])
        if self.bags and self.bags[0]:
            self.bags[0][0] = set(range(n))

    def get(self, level: int, idx: int) -> set:
        if level < len(self.bags) and idx < len(self.bags[level]):
            return self.bags[level][idx]
        return set()

def analyze_kicks(perm: list, bags: BagAssignment, t: int, level: int, idx: int):
    """Analyze sibling-native symmetry in kicks at a given rebag location."""
    n = bags.n
    ml = max_level(n)

    if level + 1 > ml:
        return None

    child_l_idx = 2 * idx
    child_r_idx = 2 * idx + 1
    if child_l_idx >= (1 << (level + 1)):
        return None

    cap = bag_capacity(n, t, level + 1)

    bag_l = bags.get(level + 1, child_l_idx)
    bag_r = bags.get(level + 1, child_r_idx)

    if not bag_l and not bag_r:
        return None

    kl, _, _ = split_bag(perm, bag_l, n, cap, level + 1)
    kr, _, _ = split_bag(perm, bag_r, n, cap, level + 1)

    if not kl and not kr:
        return None

    lo = idx * bag_size(n, level)
    boundary = lo + bag_size(n, level + 1)
    hi = lo + bag_size(n, level)

    sl, xl, nl_kl, nr_kl = 0, 0, 0, 0
    for item in kl:
        pv = perm[item]
        if is_sibling_native(n, pv, level + 1, child_l_idx):
            sl += 1
        if is_parent_stranger(n, pv, level, idx):
            xl += 1
        if lo <= pv < boundary:
            nl_kl += 1
        elif boundary <= pv < hi:
            nr_kl += 1

    sr, xr, nl_kr, nr_kr = 0, 0, 0, 0
    for item in kr:
        pv = perm[item]
        if is_sibling_native(n, pv, level + 1, child_r_idx):
            sr += 1
        if is_parent_stranger(n, pv, level, idx):
            xr += 1
        if lo <= pv < boundary:
            nl_kr += 1
        elif boundary <= pv < hi:
            nr_kr += 1

    imbalance = (nl_kl - nr_kl) + (nl_kr - nr_kr)

    return {
        'kl_size': len(kl), 'kr_size': len(kr),
        'sl': sl, 'sr': sr, 'xl': xl, 'xr': xr,
        'nl_kl': nl_kl, 'nr_kl': nr_kl, 'nl_kr': nl_kr, 'nr_kr': nr_kr,
        'imbalance': imbalance,
        'n': n, 't': t, 'level': level, 'idx': idx,
    }

def do_stage(bags: BagAssignment, perm: list, t: int) -> BagAssignment:
    n = bags.n
    ml = max_level(n)

    splits = []
    for level in range(ml + 2):
        count = min(1 << level, n)
        cap = bag_capacity(n, t, level)
        level_splits = []
        for idx in range(count):
            bag = bags.get(level, idx)
            level_splits.append(split_bag(perm, bag, n, cap, level))
        splits.append(level_splits)

    new_bags = BagAssignment.__new__(BagAssignment)
    new_bags.n = n
    new_bags.bags = []
    for level in range(ml + 2):
        count = min(1 << level, n)
        new_bags.bags.append([set() for _ in range(count)])

    for level in range(ml + 1):
        count = min(1 << level, n)
        for idx in range(count):
            child_l = 2 * idx
            child_r = 2 * idx + 1

            if level + 1 < len(splits):
                if child_l < len(splits[level + 1]):
                    new_bags.bags[level][idx].update(splits[level + 1][child_l][0])
                if child_r < len(splits[level + 1]):
                    new_bags.bags[level][idx].update(splits[level + 1][child_r][0])

            if level > 0:
                parent_idx = idx // 2
                if parent_idx < len(splits[level - 1]):
                    from_parent = splits[level - 1][parent_idx][1 if idx % 2 == 0 else 2]
                    new_bags.bags[level][idx].update(from_parent)

    return new_bags

def main():
    print("Testing sibling-native symmetry: SL vs SR in kicks\n")
    print(f"Parameters: A={A}, ν={NU}, λ={LAM}, ε={EPS}")
    print()

    max_sl_sr_diff = 0
    max_sl_sr_diff_case = ""
    total_cases = 0
    exact_equality_cases = 0
    cases_with_large_diff = 0
    max_imbalance_ratio = 0.0

    # Also track the key identity: nr_kl should equal sl
    nr_kl_ne_sl_count = 0
    nl_kr_ne_sr_count = 0

    for k in range(4, 11):
        n = 1 << k
        perm = list(range(n))  # Identity permutation
        bags = BagAssignment(n)

        for t in range(30):
            ml = max_level(n)

            for level in range(ml):
                count = min(1 << level, n)
                for idx in range(count):
                    a = analyze_kicks(perm, bags, t, level, idx)
                    if a is None:
                        continue

                    total_cases += 1
                    sl_sr_diff = abs(a['sr'] - a['sl'])

                    if a['sl'] == a['sr']:
                        exact_equality_cases += 1

                    if sl_sr_diff > max_sl_sr_diff:
                        max_sl_sr_diff = sl_sr_diff
                        max_sl_sr_diff_case = (
                            f"n={n} t={t} level={level} idx={idx}: "
                            f"|kL|={a['kl_size']} |kR|={a['kr_size']} "
                            f"SL={a['sl']} SR={a['sr']} XL={a['xl']} XR={a['xr']}"
                        )

                    # Check key identity: nr_kl should equal sl
                    if a['nr_kl'] != a['sl']:
                        nr_kl_ne_sl_count += 1
                    if a['nl_kr'] != a['sr']:
                        nl_kr_ne_sr_count += 1

                    cap_t1_level = bag_capacity(n, t + 1, level)
                    kick_bound = 2.0 * LAM * EPS * cap_t1_level
                    if kick_bound > 0.001:
                        ratio = abs(a['imbalance']) / kick_bound
                        if ratio > max_imbalance_ratio:
                            max_imbalance_ratio = ratio
                        if ratio > 1.0:
                            cases_with_large_diff += 1

            bags = do_stage(bags, perm, t)

    print("Results:")
    print(f"  Total kick analysis cases: {total_cases}")
    print(f"  Cases with SL = SR exactly: {exact_equality_cases} ({100.0 * exact_equality_cases / total_cases:.1f}%)")
    print()
    print(f"  Max |SL - SR|: {max_sl_sr_diff}")
    print(f"  Worst case: {max_sl_sr_diff_case}")
    print()
    print(f"  Max imbalance / (2·λ·ε·cap(t+1,level)) ratio: {max_imbalance_ratio:.4f}")
    print(f"  Cases exceeding kick bound: {cases_with_large_diff}")
    print()
    print("Key identity check (nr_kl should equal sl, nl_kr should equal sr):")
    print(f"  Cases where nr_kl ≠ sl: {nr_kl_ne_sl_count}")
    print(f"  Cases where nl_kr ≠ sr: {nl_kr_ne_sr_count}")

    # Print detailed analysis for a specific case where SL != SR
    print("\n--- Detailed cases where SL ≠ SR ---")
    n = 64
    perm = list(range(n))
    bags = BagAssignment(n)
    shown = 0
    for t in range(20):
        ml = max_level(n)
        for level in range(ml):
            count = min(1 << level, n)
            for idx in range(count):
                a = analyze_kicks(perm, bags, t, level, idx)
                if a and a['sl'] != a['sr'] and shown < 10:
                    print(f"  n={n} t={t} lev={level} idx={idx}: "
                          f"|kL|={a['kl_size']} |kR|={a['kr_size']} "
                          f"SL={a['sl']} SR={a['sr']} "
                          f"nLkL={a['nl_kl']} nRkL={a['nr_kl']} nLkR={a['nl_kr']} nRkR={a['nr_kr']} "
                          f"imbal={a['imbalance']}")
                    shown += 1
        bags = do_stage(bags, perm, t)

    if shown == 0:
        print("  (None found in n=64)")

if __name__ == "__main__":
    main()
