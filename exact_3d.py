"""
Exact counting of |CC([m]³)| via transfer matrix over 2D slice configs.
Uses fast boundary-based enumeration for 2D configs.
"""

import time
import sys
from collections import defaultdict


def generate_convex_2d(m):
    """Generate all convex subsets of [m]² via boundary recursion."""
    results = []

    def generate(row, last_L, last_U, had_gap, rows):
        if row == m:
            S = frozenset((i, j) for i, (l, u) in enumerate(rows)
                          if l is not None for j in range(l, u + 1))
            results.append(S)
            return

        # Empty row
        new_gap = had_gap or (last_L is not None)
        generate(row + 1, last_L, last_U, new_gap, rows + [(None, None)])

        # Nonempty row [l, u]
        for l in range(m):
            for u in range(l, m):
                if last_L is not None:
                    if had_gap:
                        if last_L <= u:
                            continue
                    else:
                        if l > last_L or u > last_U:
                            continue
                generate(row + 1, l, u, False, rows + [(l, u)])

    generate(0, None, None, False, [])
    return results


def check_3d_compatible(S1, S2):
    """Check if 2D slice configs S1, S2 are compatible for adjacent 3D layers.

    Compatible iff for all (j1,k1) ∈ S1, (j2,k2) ∈ S2 with j1≤j2, k1≤k2:
    all (j,k) with j1≤j≤j2, k1≤k≤k2 are in both S1 and S2.
    """
    for (j1, k1) in S1:
        for (j2, k2) in S2:
            if j1 <= j2 and k1 <= k2:
                for j in range(j1, j2 + 1):
                    for k in range(k1, k2 + 1):
                        if (j, k) not in S1 or (j, k) not in S2:
                            return False
    return True


def has_comparable_elements(S1, S2):
    """Check if S1 and S2 have comparable elements (j1≤j2 and k1≤k2)."""
    for (j1, k1) in S1:
        for (j2, k2) in S2:
            if j1 <= j2 and k1 <= k2:
                return True
    return False


def exact_count_3d(m):
    """Compute |CC([m]³)| exactly via transfer matrix with gap tracking."""
    print(f"  Enumerating [m]² configs...", end=" ", flush=True)
    t0 = time.time()
    configs = generate_convex_2d(m)
    n = len(configs)
    print(f"{n} configs ({time.time()-t0:.1f}s)")

    # Find empty config index
    empty_idx = None
    for i, S in enumerate(configs):
        if len(S) == 0:
            empty_idx = i
            break

    # Precompute compatibility (adjacent, no gap)
    print(f"  Building compatibility matrix ({n}×{n})...", end=" ", flush=True)
    t1 = time.time()
    compat = {}
    for i in range(n):
        if i % 1000 == 0 and i > 0:
            elapsed = time.time() - t1
            eta = elapsed / i * (n - i)
            print(f"\n    {i}/{n} ({elapsed:.0f}s elapsed, ~{eta:.0f}s remaining)...",
                  end=" ", flush=True)
        row = []
        for j in range(n):
            if i == empty_idx or j == empty_idx:
                row.append(True)
            else:
                row.append(check_3d_compatible(configs[i], configs[j]))
        compat[i] = row
    print(f"({time.time()-t1:.1f}s)")

    # Precompute comparable-elements check (for gap handling)
    print(f"  Precomputing comparable-elements...", end=" ", flush=True)
    t2 = time.time()
    comparable = {}
    for i in range(n):
        if i == empty_idx:
            comparable[i] = set()
            continue
        comp_set = set()
        for j in range(n):
            if j == empty_idx:
                continue
            if has_comparable_elements(configs[i], configs[j]):
                comp_set.add(j)
        comparable[i] = comp_set
    print(f"({time.time()-t2:.1f}s)")

    # Gap-aware DP
    print(f"  Running DP over {m} layers...", end=" ", flush=True)
    t3 = time.time()
    NONE = n
    dp = defaultdict(int)
    for c in range(n):
        if c == empty_idx:
            dp[(NONE, False)] += 1
        else:
            dp[(c, False)] += 1

    for layer in range(1, m):
        new_dp = defaultdict(int)
        for (last_ne, had_gap), count in dp.items():
            for c in range(n):
                if c == empty_idx:
                    new_gap = True if last_ne < n else had_gap
                    new_dp[(last_ne, new_gap)] += count
                else:
                    if last_ne >= n:
                        new_dp[(c, False)] += count
                    elif had_gap:
                        if c not in comparable[last_ne]:
                            new_dp[(c, False)] += count
                    else:
                        if compat[last_ne][c]:
                            new_dp[(c, False)] += count
        dp = new_dp

    total = sum(dp.values())
    print(f"({time.time()-t3:.1f}s)")
    return total


if __name__ == '__main__':
    for m in [2, 3, 4, 5]:
        print(f"\nm={m}:")
        t0 = time.time()
        c = exact_count_3d(m)
        dt = time.time() - t0
        rho_area = c ** (1.0 / m ** 2)
        print(f"  |CC([{m}]³)| = {c}")
        print(f"  |CC|^{{1/m²}} = {rho_area:.6f}")
        print(f"  Total time: {dt:.1f}s")
