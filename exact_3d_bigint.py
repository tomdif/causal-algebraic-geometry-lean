"""
Exact |CC([m]³)| with Python big integers and C-accelerated boolean checks.
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
            results.append((list(L), list(U)))
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

    # Pack into C array
    configs_flat = np.zeros(n * 2 * m, dtype=np.int32)
    for i, (L, U) in enumerate(configs):
        for j in range(m):
            configs_flat[i * 2 * m + j] = L[j]
            configs_flat[i * 2 * m + m + j] = U[j]
    configs_ptr = configs_flat.ctypes.data_as(ctypes.POINTER(ctypes.c_int))

    # DP with Python big integers
    # dp_adj[i] = Python int, state (i, had_gap=False)
    # dp_gap[i] = Python int, state (i, had_gap=True)
    dp_adj = [0] * n  # Python ints (arbitrary precision)
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
        new_none = dp_none  # empty → empty preserves NONE state

        # (i, *) → empty → (i, gap=True)
        for i in range(n):
            if i == empty_idx:
                continue
            new_gap[i] += dp_adj[i] + dp_gap[i]

        # For each nonempty target c, sum contributions:
        # Build list of nonzero dp entries for efficiency
        active_adj = [(i, dp_adj[i]) for i in range(n) if dp_adj[i] > 0 and i != empty_idx]
        active_gap = [(i, dp_gap[i]) for i in range(n) if dp_gap[i] > 0 and i != empty_idx]

        total_from_none = dp_none

        n_active = len(active_adj) + len(active_gap)
        print(f"    layer {layer+1}/{m}: {len(active_adj)} adj + {len(active_gap)} gap...",
              end=" ", flush=True)

        for c in range(n):
            if c == empty_idx:
                continue

            # From NONE → c
            new_adj[c] += total_from_none

            # From adj states
            for i, val in active_adj:
                if _lib.check_one_compatible(configs_ptr, i, c, m):
                    new_adj[c] += val

            # From gap states
            for i, val in active_gap:
                if not _lib.check_one_comparable(configs_ptr, i, c, m):
                    new_adj[c] += val

        dp_adj = new_adj
        dp_gap = new_gap
        dp_none = new_none

        dt = time.time() - t1
        print(f"{dt:.1f}s")

    total = sum(dp_adj) + sum(dp_gap) + dp_none
    return total


if __name__ == '__main__':
    from math import log

    known = {2: 101, 3: 129535, 4: 4664028094, 5: 4725549877891433}

    # Quick verification
    for m in [2, 3, 4]:
        c = exact_count_3d(m)
        match = "✓" if c == known[m] else f"✗ (got {c})"
        print(f"  |CC([{m}]³)| = {c} {match}\n")

    # m=5 verification
    print("m=5:")
    c5 = exact_count_3d(5)
    match = "✓" if c5 == known[5] else f"✗ (got {c5})"
    print(f"  |CC([5]³)| = {c5} {match}\n")

    # m=6 — the target
    print("m=6:")
    t0 = time.time()
    c6 = exact_count_3d(6)
    dt = time.time() - t0
    rho = c6 ** (1.0 / 36)
    print(f"  |CC([6]³)| = {c6}")
    print(f"  |CC|^{{1/36}} = {rho:.6f}")
    print(f"  Time: {dt:.1f}s")
    print()

    # Analysis with all 5 data points
    print("=== GROWTH RATE ANALYSIS ===")
    vals = dict(known)
    vals[6] = c6
    import numpy as np

    ms = np.array([2, 3, 4, 5, 6], dtype=float)
    log_cc = np.array([log(vals[m]) for m in [2, 3, 4, 5, 6]])

    # Fit: log|CC| = a·m² + b·m + c
    A = np.vstack([ms**2, ms, np.ones(5)]).T
    coeffs = np.linalg.lstsq(A, log_cc, rcond=None)[0]
    print(f"  log|CC| = {coeffs[0]:.6f}·m² + {coeffs[1]:.6f}·m + {coeffs[2]:.4f}")
    print(f"  ρ₃ = exp({coeffs[0]:.6f}) = {np.exp(coeffs[0]):.6f}")
    print(f"  β₃ = {-coeffs[1]:.6f} (linear sub-leading coefficient)")

    # Fit with log(m) term
    A2 = np.vstack([ms**2, ms, np.log(ms), np.ones(5)]).T
    coeffs2 = np.linalg.lstsq(A2, log_cc, rcond=None)[0]
    print(f"\n  With log(m): {coeffs2[0]:.6f}·m² + {coeffs2[1]:.6f}·m + {coeffs2[2]:.4f}·log(m) + {coeffs2[3]:.4f}")
    print(f"  ρ₃ = exp({coeffs2[0]:.6f}) = {np.exp(coeffs2[0]):.6f}")

    # Residuals
    resid1 = log_cc - A @ coeffs
    resid2 = log_cc - A2 @ coeffs2
    print(f"\n  RSS (quadratic): {np.sum(resid1**2):.10f}")
    print(f"  RSS (with log):  {np.sum(resid2**2):.10f}")
