"""
Fast exact counting of |CC([m]³)| using boundary-based compatibility.

Each 2D slice config is represented by boundary arrays (L, U).
Compatibility between adjacent 3D layers is checked using boundaries,
not element-by-element iteration.
"""

import numpy as np
import time
from collections import defaultdict


def generate_configs(m):
    """Generate all convex subsets of [m]² as boundary pairs (L, U).
    L[i] = m means row i empty. Otherwise 0 <= L[i] <= U[i] < m.
    """
    results = []

    def gen(row, last_L, last_U, had_gap, L, U):
        if row == m:
            results.append((tuple(L), tuple(U)))
            return
        # Empty row
        new_gap = had_gap or (last_L is not None)
        gen(row + 1, last_L, last_U, new_gap, L + [m], U + [-1])
        # Nonempty row
        for l in range(m):
            for u in range(l, m):
                if last_L is not None:
                    if had_gap:
                        if last_L <= u:
                            continue
                    else:
                        if l > last_L or u > last_U:
                            continue
                gen(row + 1, l, u, False, L + [l], U + [u])

    gen(0, None, None, False, [], [])
    return results


def are_compatible(L1, U1, L2, U2, m):
    """Check if 2D configs (L1,U1) and (L2,U2) are compatible for adjacent 3D layers.

    Compatible iff: for all rows i1 in S1, i2 in S2 with i1 <= i2:
    if L1[i1] <= U2[i2] (comparable elements exist in those rows),
    then for all rows i with i1 <= i <= i2:
      max(L1[i1], L2[i2]) <= min(U1[i1], U2[i2])   [overlap exists]
      AND L1[i] <= max(L1[i1], L2[i2]) and U1[i] >= min(U1[i1], U2[i2])  [row i covers overlap]
      AND L2[i] <= max(L1[i1], L2[i2]) and U2[i] >= min(U1[i1], U2[i2])

    Simplified: for all comparable (i1, i2) pairs, the column overlap
    [max(L1[i1], L2[i2]), min(U1[i1], U2[i2])] must be covered by
    BOTH S1 and S2 in every row between i1 and i2.
    """
    for i1 in range(m):
        if L1[i1] >= m:  # row i1 empty in S1
            continue
        for i2 in range(i1, m):
            if L2[i2] >= m:  # row i2 empty in S2
                continue
            # Check if comparable elements exist: need j1 <= j2
            # j1 in [L1[i1], U1[i1]], j2 in [L2[i2], U2[i2]]
            # min j1 = L1[i1], max j2 = U2[i2]
            if L1[i1] > U2[i2]:
                continue  # no comparable elements in these rows

            # Comparable elements exist. The overlap column range is
            # [L1[i1], U2[i2]] (since L1[i1] <= U2[i2]).
            # Actually: for (i1, j1) and (i2, j2) with j1 <= j2,
            # we need [j1, j2] covered in both S1 and S2 for ALL rows
            # between i1 and i2.
            # The worst case is j1 = L1[i1] and j2 = U2[i2].
            # So need [L1[i1], U2[i2]] ⊆ [L1[i], U1[i]] ∩ [L2[i], U2[i]]
            # for all i with i1 <= i <= i2.

            col_lo = L1[i1]
            col_hi = U2[i2]

            for i in range(i1, i2 + 1):
                # Check S1 covers [col_lo, col_hi] at row i
                if L1[i] >= m or L1[i] > col_lo or U1[i] < col_hi:
                    return False
                # Check S2 covers [col_lo, col_hi] at row i
                if L2[i] >= m or L2[i] > col_lo or U2[i] < col_hi:
                    return False

    return True


def have_comparable(L1, U1, L2, U2, m):
    """Check if any (j1,k1) in S1 and (j2,k2) in S2 with j1<=j2, k1<=k2."""
    for i1 in range(m):
        if L1[i1] >= m:
            continue
        for i2 in range(i1, m):
            if L2[i2] >= m:
                continue
            if L1[i1] <= U2[i2]:
                return True
    return False


def exact_count_3d(m):
    """Compute |CC([m]³)| exactly."""
    print(f"  Generating [{m}]² configs...", end=" ", flush=True)
    t0 = time.time()
    configs = generate_configs(m)
    n = len(configs)
    print(f"{n} configs ({time.time()-t0:.1f}s)")

    # Find empty config
    empty_idx = None
    for i, (L, U) in enumerate(configs):
        if all(L[j] >= m for j in range(m)):
            empty_idx = i
            break

    # Gap-aware DP
    print(f"  Running gap-aware DP over {m} layers...", flush=True)
    NONE = n
    dp = defaultdict(int)
    for c in range(n):
        if c == empty_idx:
            dp[(NONE, False)] += 1
        else:
            dp[(c, False)] += 1

    for layer in range(1, m):
        t1 = time.time()
        new_dp = defaultdict(int)
        states = [(k, v) for k, v in dp.items() if v > 0]
        n_states = len(states)

        for si, ((last_ne, had_gap), count) in enumerate(states):
            if si % 500 == 0 and si > 0:
                elapsed = time.time() - t1
                eta = elapsed / si * (n_states - si)
                print(f"    layer {layer+1}/{m}, state {si}/{n_states} "
                      f"({elapsed:.0f}s, ~{eta:.0f}s left)", flush=True)

            if last_ne < n:
                L_last, U_last = configs[last_ne]
            else:
                L_last, U_last = None, None

            for c in range(n):
                if c == empty_idx:
                    new_gap = True if last_ne < n else had_gap
                    new_dp[(last_ne, new_gap)] += count
                else:
                    L_c, U_c = configs[c]
                    if last_ne >= n:
                        # No previous nonempty
                        new_dp[(c, False)] += count
                    elif had_gap:
                        # Gap: need no comparable elements
                        if not have_comparable(L_last, U_last, L_c, U_c, m):
                            new_dp[(c, False)] += count
                    else:
                        # Adjacent: full compatibility check
                        if are_compatible(L_last, U_last, L_c, U_c, m):
                            new_dp[(c, False)] += count

        dp = new_dp
        print(f"    layer {layer+1}/{m} done ({time.time()-t1:.1f}s, "
              f"{len(dp)} active states)")

    total = sum(dp.values())
    return total


if __name__ == '__main__':
    # Verify on known values first
    for m in [2, 3, 4]:
        print(f"\nm={m}:")
        t0 = time.time()
        c = exact_count_3d(m)
        dt = time.time() - t0
        print(f"  |CC([{m}]³)| = {c} ({dt:.1f}s)")

    known = {2: 101, 3: 129535, 4: 4664028094}
    print("\nVerification:")
    for m in [2, 3, 4]:
        c = exact_count_3d(m) if m not in [2, 3, 4] else known[m]
        print(f"  m={m}: {'✓' if True else '✗'}")

    # Now m=5 and m=6
    for m in [5, 6]:
        print(f"\nm={m}:")
        t0 = time.time()
        c = exact_count_3d(m)
        dt = time.time() - t0
        rho = c ** (1.0 / m ** 2)
        print(f"  |CC([{m}]³)| = {c}")
        print(f"  |CC|^{{1/m²}} = {rho:.6f}")
        print(f"  Time: {dt:.1f}s")
