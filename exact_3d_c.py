"""
Fast exact counting of |CC([m]³)| using C-accelerated compatibility check.
"""

import numpy as np
import ctypes
import time
import os

# Load C library
_dir = os.path.dirname(os.path.abspath(__file__))
_lib = ctypes.CDLL(os.path.join(_dir, 'compat_check.so'))

_lib.sum_compatible.restype = ctypes.c_int64
_lib.sum_compatible.argtypes = [
    ctypes.POINTER(ctypes.c_int),  # L1
    ctypes.POINTER(ctypes.c_int),  # U1
    ctypes.POINTER(ctypes.c_int),  # configs (flat)
    ctypes.POINTER(ctypes.c_int64),  # dp_vals
    ctypes.c_int,  # n
    ctypes.c_int,  # m
    ctypes.c_int,  # mode
    ctypes.c_int,  # empty_idx
]


def generate_configs(m):
    """Generate all convex subsets of [m]² as boundary pairs."""
    results = []

    def gen(row, last_L, last_U, had_gap, L, U):
        if row == m:
            results.append((list(L), list(U)))
            return
        new_gap = had_gap or (last_L is not None)
        gen(row + 1, last_L, last_U, new_gap, L + [m], U + [-1])
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


def exact_count_3d(m):
    """Compute |CC([m]³)| exactly using C-accelerated DP."""
    print(f"  Generating [{m}]² configs...", end=" ", flush=True)
    t0 = time.time()
    configs = generate_configs(m)
    n = len(configs)
    print(f"{n} configs ({time.time()-t0:.1f}s)")

    # Find empty config
    empty_idx = -1
    for i, (L, U) in enumerate(configs):
        if all(L[j] >= m for j in range(m)):
            empty_idx = i
            break

    # Pack configs into flat C array
    configs_flat = np.zeros(n * 2 * m, dtype=np.int32)
    for i, (L, U) in enumerate(configs):
        for j in range(m):
            configs_flat[i * 2 * m + j] = L[j]
            configs_flat[i * 2 * m + m + j] = U[j]

    configs_ptr = configs_flat.ctypes.data_as(ctypes.POINTER(ctypes.c_int))

    # DP arrays
    # State: (last_nonempty_idx, had_gap)
    # Flatten: dp_adj[i] = count for state (i, False)
    #          dp_gap[i] = count for state (i, True)
    #          dp_none_adj = count for state (NONE, False)
    #          dp_none_gap = count for state (NONE, True)

    dp_adj = np.zeros(n, dtype=np.int64)  # (i, had_gap=False)
    dp_gap = np.zeros(n, dtype=np.int64)  # (i, had_gap=True)
    dp_none = np.int64(0)  # (NONE, False) — no nonempty yet, no gap

    # Initialize layer 0
    for c in range(n):
        if c == empty_idx:
            dp_none += 1
        else:
            dp_adj[c] = 1

    for layer in range(1, m):
        t1 = time.time()
        new_adj = np.zeros(n, dtype=np.int64)
        new_gap = np.zeros(n, dtype=np.int64)
        new_none = np.int64(0)

        # Process empty config transitions
        # Any state → empty config: increment dp_none or dp_gap
        # (NONE, False) → empty → (NONE, False)
        new_none += dp_none
        # (i, False) → empty → (i, True)  for each nonempty i
        # (i, True) → empty → (i, True)   for each nonempty i
        for i in range(n):
            if i == empty_idx:
                continue
            new_gap[i] += dp_adj[i] + dp_gap[i]

        # Process nonempty config transitions using C
        total_adj = int(np.sum(dp_adj))
        total_gap = int(np.sum(dp_gap))

        dp_adj_ptr = dp_adj.ctypes.data_as(ctypes.POINTER(ctypes.c_int64))
        dp_gap_ptr = dp_gap.ctypes.data_as(ctypes.POINTER(ctypes.c_int64))

        n_active_adj = int(np.count_nonzero(dp_adj))
        n_active_gap = int(np.count_nonzero(dp_gap))

        print(f"    layer {layer+1}/{m}: {n_active_adj} adj + {n_active_gap} gap "
              f"active states...", end=" ", flush=True)

        for c in range(n):
            if c == empty_idx:
                continue

            L_c = configs_flat[c * 2 * m: c * 2 * m + m]
            U_c = configs_flat[c * 2 * m + m: c * 2 * m + 2 * m]
            L_c_ptr = L_c.ctypes.data_as(ctypes.POINTER(ctypes.c_int))
            U_c_ptr = U_c.ctypes.data_as(ctypes.POINTER(ctypes.c_int))

            # From (NONE, *) → (c, False)
            new_adj[c] += dp_none

            # From (i, False) → (c, False) if compatible(i, c)
            if total_adj > 0:
                s = _lib.sum_compatible(L_c_ptr, U_c_ptr, configs_ptr,
                                        dp_adj_ptr, n, m, 0, empty_idx)
                new_adj[c] += s

            # From (i, True) → (c, False) if no comparable(i, c)
            if total_gap > 0:
                s = _lib.sum_compatible(L_c_ptr, U_c_ptr, configs_ptr,
                                        dp_gap_ptr, n, m, 1, empty_idx)
                new_adj[c] += s

        dp_adj = new_adj
        dp_gap = new_gap
        dp_none = new_none

        dt = time.time() - t1
        total = int(np.sum(dp_adj) + np.sum(dp_gap) + dp_none)
        print(f"{dt:.1f}s")

    total = int(np.sum(dp_adj) + np.sum(dp_gap) + dp_none)
    return total


if __name__ == '__main__':
    from math import log

    # Verify
    known = {2: 101, 3: 129535, 4: 4664028094, 5: 4725549877891433}

    for m in [2, 3, 4]:
        print(f"\nm={m}:")
        t0 = time.time()
        c = exact_count_3d(m)
        dt = time.time() - t0
        expected = known[m]
        match = "✓" if c == expected else f"✗ (got {c}, expected {expected})"
        print(f"  |CC([{m}]³)| = {c} {match} ({dt:.1f}s)")

    # m=5 (timing test)
    print(f"\nm=5:")
    t0 = time.time()
    c5 = exact_count_3d(5)
    dt = time.time() - t0
    match = "✓" if c5 == known[5] else f"✗ (got {c5})"
    print(f"  |CC([5]³)| = {c5} {match} ({dt:.1f}s)")

    # m=6 (the target)
    print(f"\nm=6:")
    t0 = time.time()
    c6 = exact_count_3d(6)
    dt = time.time() - t0
    rho = c6 ** (1.0 / 36)
    print(f"  |CC([6]³)| = {c6}")
    print(f"  |CC|^{{1/36}} = {rho:.6f}")
    print(f"  Time: {dt:.1f}s")
