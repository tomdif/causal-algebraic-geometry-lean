"""
Exact |CC([m]³)| — Python bigints for DP, C for sum-of-compatibles per config.

Strategy: DP values stored as Python ints (arbitrary precision).
For each target config c, call C once to get sum of Python ints over
compatible source configs. Sum is done in Python, compatibility checks in C.

Batched compatibility check: C returns a bitmask (or list of compatible indices).
Then Python sums the corresponding dp values.
"""

import numpy as np
import ctypes
import time
import os

_dir = os.path.dirname(os.path.abspath(__file__))
_lib = ctypes.CDLL(os.path.join(_dir, 'compat_check.so'))

_lib.check_one_compatible.restype = ctypes.c_int
_lib.check_one_compatible.argtypes = [
    ctypes.POINTER(ctypes.c_int), ctypes.c_int, ctypes.c_int, ctypes.c_int
]
_lib.check_one_comparable.restype = ctypes.c_int
_lib.check_one_comparable.argtypes = [
    ctypes.POINTER(ctypes.c_int), ctypes.c_int, ctypes.c_int, ctypes.c_int
]


def generate_configs(m):
    results = []
    def gen(row, last_L, last_U, had_gap, L, U):
        if row == m:
            results.append((tuple(L), tuple(U)))
            return
        new_gap = had_gap or (last_L is not None)
        gen(row + 1, last_L, last_U, new_gap, L + [m], U + [-1])
        for l in range(m):
            for u in range(l, m):
                if last_L is not None:
                    if had_gap:
                        if last_L <= u: continue
                    else:
                        if l > last_L or u > last_U: continue
                gen(row + 1, l, u, False, L + [l], U + [u])
    gen(0, None, None, False, [], [])
    return results


def exact_count_3d(m):
    print(f"  Generating [{m}]² configs...", end=" ", flush=True)
    t0 = time.time()
    configs = generate_configs(m)
    n = len(configs)
    print(f"{n} configs ({time.time()-t0:.1f}s)")

    empty_idx = -1
    for i, (L, U) in enumerate(configs):
        if all(L[j] >= m for j in range(m)):
            empty_idx = i
            break

    # Pack configs
    configs_flat = np.zeros(n * 2 * m, dtype=np.int32)
    for i, (L, U) in enumerate(configs):
        for j in range(m):
            configs_flat[i * 2 * m + j] = L[j]
            configs_flat[i * 2 * m + m + j] = U[j]
    configs_ptr = configs_flat.ctypes.data_as(ctypes.POINTER(ctypes.c_int))

    # Precompute compatibility matrix as adjacency LISTS
    # For each i, store list of j such that compat(i, j)
    # Same for "have_comparable"
    print(f"  Building adjacency lists for {n} configs...", end=" ", flush=True)
    t1 = time.time()

    # Use numpy for temporary storage, then convert to Python lists
    compat_lists = [None] * n
    comparable_lists = [None] * n

    for i in range(n):
        if i == empty_idx:
            compat_lists[i] = []
            comparable_lists[i] = []
            continue
        if i % 10000 == 0 and i > 0:
            elapsed = time.time() - t1
            eta = elapsed / i * (n - i)
            print(f"\n    {i}/{n} ({elapsed:.0f}s, ~{eta:.0f}s left)",
                  end=" ", flush=True)

        c_list = []
        comp_list = []
        for j in range(n):
            if j == empty_idx:
                continue
            if _lib.check_one_compatible(configs_ptr, i, j, m):
                c_list.append(j)
            if _lib.check_one_comparable(configs_ptr, i, j, m):
                comp_list.append(j)
        compat_lists[i] = c_list
        comparable_lists[i] = comp_list

    print(f"({time.time()-t1:.0f}s)")

    # DP with Python bigints
    dp_adj = [0] * n
    dp_gap = [0] * n
    dp_none = 0

    for c in range(n):
        if c == empty_idx:
            dp_none += 1
        else:
            dp_adj[c] = 1

    for layer in range(1, m):
        t1 = time.time()
        new_adj = [0] * n
        new_gap = [0] * n
        new_none = dp_none

        # (i, *) → empty → (i, gap=True)
        for i in range(n):
            if i == empty_idx:
                continue
            new_gap[i] = dp_adj[i] + dp_gap[i]

        # For each target c: sum dp_adj over compatible, dp_gap over "not comparable"
        # "Not comparable" = all j except those in comparable_lists[i]
        # But we need to invert the relation: for each c, which i's satisfy
        # i is compatible with c  vs  i is NOT comparable with c.
        # Since both relations are symmetric (check carefully), we can use c's lists.

        total_from_none = dp_none

        for c in range(n):
            if c == empty_idx:
                continue

            contrib = total_from_none

            # Sum dp_adj[i] over i compatible with c
            # Compatibility: compat(last_ne, new_c) — is this symmetric?
            # are_compatible(L1, U1, L2, U2): asymmetric (i1 <= i2 direction)
            # So compat_lists[c] might not equal compat_lists[i] reversed.
            # But we stored compat_lists[i] = {j : compat(i, j)}.
            # We need: sum over i where compat(i, c).
            # This is {i : c in compat_lists[i]}. Inverse index!

            # We should precompute the REVERSE adjacency: for each j,
            # the list of i's that have j in compat_lists[i].
            pass  # handled below after precomputation

        # Build reverse adjacency
        compat_rev = [[] for _ in range(n)]
        comp_rev = [[] for _ in range(n)]
        for i in range(n):
            if compat_lists[i] is None:
                continue
            for j in compat_lists[i]:
                compat_rev[j].append(i)
            for j in comparable_lists[i]:
                comp_rev[j].append(i)

        # For gap mode: contribution from (i, gap=True) to (c, gap=False)
        # requires NOT comparable(i, c). That's i NOT in comp_rev[c].
        # Total dp_gap sum minus sum over comp_rev[c].
        total_dp_gap = sum(dp_gap)

        for c in range(n):
            if c == empty_idx:
                continue

            # From NONE
            contrib = total_from_none

            # From (i, adj): i where compat(i, c) → i in compat_rev[c]
            for i in compat_rev[c]:
                contrib += dp_adj[i]

            # From (i, gap): i where NOT comparable(i, c)
            # = total - (sum over i in comp_rev[c] of dp_gap[i])
            sub = 0
            for i in comp_rev[c]:
                sub += dp_gap[i]
            contrib += (total_dp_gap - sub)

            new_adj[c] = contrib

        dp_adj = new_adj
        dp_gap = new_gap
        dp_none = new_none

        dt = time.time() - t1
        total = dp_none + sum(dp_adj) + sum(dp_gap)
        print(f"    layer {layer+1}/{m}: {dt:.1f}s")

    return dp_none + sum(dp_adj) + sum(dp_gap)


if __name__ == '__main__':
    from math import log
    import numpy as np

    known = {2: 101, 3: 129535, 4: 4664028094, 5: 4725549877891433}

    for m in [2, 3, 4]:
        print(f"m={m}:")
        c = exact_count_3d(m)
        match = "✓" if c == known[m] else f"✗ (got {c})"
        print(f"  |CC([{m}]³)| = {c} {match}\n")

    # m=5 (timing check)
    print("m=5:")
    t0 = time.time()
    c5 = exact_count_3d(5)
    dt = time.time() - t0
    match = "✓" if c5 == known[5] else f"✗ (got {c5})"
    print(f"  |CC([5]³)| = {c5} {match} ({dt:.1f}s)\n")

    # m=6
    print("m=6:")
    t0 = time.time()
    c6 = exact_count_3d(6)
    dt = time.time() - t0
    rho = c6 ** (1.0 / 36)
    print(f"  |CC([6]³)| = {c6}")
    print(f"  |CC|^{{1/36}} = {rho:.6f}")
    print(f"  Time: {dt:.1f}s")

    # Analysis
    vals = dict(known)
    vals[6] = c6
    ms = np.array([2, 3, 4, 5, 6], dtype=float)
    log_cc = np.array([log(vals[m]) for m in [2, 3, 4, 5, 6]])

    print("\n=== FIT ANALYSIS ===\n")

    A1 = np.vstack([ms**2, ms, np.ones(5)]).T
    c1 = np.linalg.lstsq(A1, log_cc, rcond=None)[0]
    resid1 = log_cc - A1 @ c1
    print(f"Quadratic fit: log|CC| = {c1[0]:.6f}·m² + {c1[1]:.6f}·m + {c1[2]:.4f}")
    print(f"  ρ₃ = {np.exp(c1[0]):.6f}")
    print(f"  RSS = {np.sum(resid1**2):.10f}")

    A2 = np.vstack([ms**2, ms, np.log(ms), np.ones(5)]).T
    c2 = np.linalg.lstsq(A2, log_cc, rcond=None)[0]
    resid2 = log_cc - A2 @ c2
    print(f"\nWith log(m): {c2[0]:.6f}·m² + {c2[1]:.6f}·m + {c2[2]:.4f}·log(m) + {c2[3]:.4f}")
    print(f"  ρ₃ = {np.exp(c2[0]):.6f}")
    print(f"  log(m) coef = {c2[2]:.4f}")
    print(f"  RSS = {np.sum(resid2**2):.10f}")

    print("\nρ_m = |CC|^{1/m²}:")
    for m in [2, 3, 4, 5, 6]:
        print(f"  m={m}: {vals[m] ** (1.0/m**2):.6f}")
