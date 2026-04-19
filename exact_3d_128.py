"""
Exact |CC([m]³)| using __int128 C accumulator.

Represents each accumulator as (high, low) int64 pair.
"""

import numpy as np
import ctypes
import time
import os

_dir = os.path.dirname(os.path.abspath(__file__))
_lib = ctypes.CDLL(os.path.join(_dir, 'compat_check.so'))

_lib.sum_compatible_128.restype = None
_lib.sum_compatible_128.argtypes = [
    ctypes.POINTER(ctypes.c_int),      # L1
    ctypes.POINTER(ctypes.c_int),      # U1
    ctypes.POINTER(ctypes.c_int),      # configs
    ctypes.POINTER(ctypes.c_int64),    # dp_hi
    ctypes.POINTER(ctypes.c_int64),    # dp_lo
    ctypes.c_int,                       # n
    ctypes.c_int,                       # m
    ctypes.c_int,                       # mode (0=compat, 1=gap)
    ctypes.c_int,                       # empty_idx
    ctypes.POINTER(ctypes.c_int64),    # out_hi
    ctypes.POINTER(ctypes.c_int64),    # out_lo
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


def to_hi_lo(big_int):
    """Convert Python int to (high, low) int64 pair (unsigned low)."""
    low = big_int & ((1 << 64) - 1)
    high = big_int >> 64
    # Convert to signed int64 range
    if low >= (1 << 63):
        low -= (1 << 64)
    if high >= (1 << 63):
        high -= (1 << 64)
    return high, low


def from_hi_lo(hi, lo):
    """Convert (high, low) int64 pair back to Python int."""
    # Treat lo as unsigned
    if lo < 0:
        lo += (1 << 64)
    return (hi << 64) | lo


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

    # DP arrays stored as (hi, lo) int64 pairs
    dp_adj_hi = np.zeros(n, dtype=np.int64)
    dp_adj_lo = np.zeros(n, dtype=np.int64)
    dp_gap_hi = np.zeros(n, dtype=np.int64)
    dp_gap_lo = np.zeros(n, dtype=np.int64)
    dp_none = 0  # Python int

    # Initialize
    for c in range(n):
        if c == empty_idx:
            dp_none += 1
        else:
            dp_adj_lo[c] = 1

    out_hi = ctypes.c_int64(0)
    out_lo = ctypes.c_int64(0)

    for layer in range(1, m):
        t1 = time.time()
        new_adj_hi = np.zeros(n, dtype=np.int64)
        new_adj_lo = np.zeros(n, dtype=np.int64)
        new_gap_hi = np.zeros(n, dtype=np.int64)
        new_gap_lo = np.zeros(n, dtype=np.int64)
        new_none = dp_none  # empty → empty preserves NONE state

        # (i, *) → empty → (i, gap=True) for each nonempty i
        for i in range(n):
            if i == empty_idx:
                continue
            total_i = (from_hi_lo(dp_adj_hi[i], dp_adj_lo[i]) +
                       from_hi_lo(dp_gap_hi[i], dp_gap_lo[i]))
            hi, lo = to_hi_lo(total_i)
            new_gap_hi[i] = hi
            new_gap_lo[i] = lo

        dp_adj_hi_ptr = dp_adj_hi.ctypes.data_as(ctypes.POINTER(ctypes.c_int64))
        dp_adj_lo_ptr = dp_adj_lo.ctypes.data_as(ctypes.POINTER(ctypes.c_int64))
        dp_gap_hi_ptr = dp_gap_hi.ctypes.data_as(ctypes.POINTER(ctypes.c_int64))
        dp_gap_lo_ptr = dp_gap_lo.ctypes.data_as(ctypes.POINTER(ctypes.c_int64))

        print(f"    layer {layer+1}/{m}...", end=" ", flush=True)

        for c in range(n):
            if c == empty_idx:
                continue

            # Sum contributions for (c, False)
            contrib = dp_none  # from NONE

            # From adj states via C
            L_c = configs_flat[c * 2 * m: c * 2 * m + m]
            U_c = configs_flat[c * 2 * m + m: c * 2 * m + 2 * m]
            L_c_ptr = L_c.ctypes.data_as(ctypes.POINTER(ctypes.c_int))
            U_c_ptr = U_c.ctypes.data_as(ctypes.POINTER(ctypes.c_int))

            _lib.sum_compatible_128(L_c_ptr, U_c_ptr, configs_ptr,
                                     dp_adj_hi_ptr, dp_adj_lo_ptr,
                                     n, m, 0, empty_idx,
                                     ctypes.byref(out_hi), ctypes.byref(out_lo))
            contrib += from_hi_lo(out_hi.value, out_lo.value)

            _lib.sum_compatible_128(L_c_ptr, U_c_ptr, configs_ptr,
                                     dp_gap_hi_ptr, dp_gap_lo_ptr,
                                     n, m, 1, empty_idx,
                                     ctypes.byref(out_hi), ctypes.byref(out_lo))
            contrib += from_hi_lo(out_hi.value, out_lo.value)

            hi, lo = to_hi_lo(contrib)
            new_adj_hi[c] = hi
            new_adj_lo[c] = lo

        dp_adj_hi = new_adj_hi
        dp_adj_lo = new_adj_lo
        dp_gap_hi = new_gap_hi
        dp_gap_lo = new_gap_lo
        dp_none = new_none

        dt = time.time() - t1
        print(f"{dt:.1f}s")

    total = dp_none
    for i in range(n):
        total += from_hi_lo(dp_adj_hi[i], dp_adj_lo[i])
        total += from_hi_lo(dp_gap_hi[i], dp_gap_lo[i])

    return total


if __name__ == '__main__':
    from math import log
    import numpy as np

    known = {2: 101, 3: 129535, 4: 4664028094, 5: 4725549877891433}

    # Verify m=2 through 5
    for m in [2, 3, 4, 5]:
        print(f"m={m}:")
        c = exact_count_3d(m)
        match = "✓" if c == known[m] else f"✗ (got {c})"
        print(f"  |CC([{m}]³)| = {c} {match}\n")

    # m=6: the target
    print("m=6:")
    t0 = time.time()
    c6 = exact_count_3d(6)
    dt = time.time() - t0
    rho = c6 ** (1.0 / 36)
    print(f"  |CC([6]³)| = {c6}")
    print(f"  |CC|^{{1/36}} = {rho:.6f}")
    print(f"  Time: {dt:.1f}s\n")

    # Growth analysis
    vals = dict(known)
    vals[6] = c6

    print("=== GROWTH RATE ANALYSIS WITH m=2..6 ===\n")

    ms = np.array([2, 3, 4, 5, 6], dtype=float)
    log_cc = np.array([log(vals[m]) for m in [2, 3, 4, 5, 6]])

    # Model 1: log|CC| = a·m² + b·m + c
    A1 = np.vstack([ms**2, ms, np.ones(5)]).T
    c1 = np.linalg.lstsq(A1, log_cc, rcond=None)[0]
    resid1 = log_cc - A1 @ c1
    print(f"Model 1 (quadratic): {c1[0]:.6f}·m² + {c1[1]:.6f}·m + {c1[2]:.4f}")
    print(f"  ρ₃ = {np.exp(c1[0]):.6f}, β₃ = {-c1[1]:.6f}")
    print(f"  RSS = {np.sum(resid1**2):.10f}")

    # Model 2: log|CC| = a·m² + b·m + c·log(m) + d
    A2 = np.vstack([ms**2, ms, np.log(ms), np.ones(5)]).T
    c2 = np.linalg.lstsq(A2, log_cc, rcond=None)[0]
    resid2 = log_cc - A2 @ c2
    print(f"\nModel 2 (+log): {c2[0]:.6f}·m² + {c2[1]:.6f}·m + {c2[2]:.4f}·log(m) + {c2[3]:.4f}")
    print(f"  ρ₃ = {np.exp(c2[0]):.6f}, β₃ = {-c2[1]:.6f}, α_log = {c2[2]:.6f}")
    print(f"  RSS = {np.sum(resid2**2):.10f}")

    # Richardson: ρ(m) = |CC|^{1/m²}
    print("\nRichardson extrapolation of ρ₃:")
    for m in [2, 3, 4, 5, 6]:
        rho_m = vals[m] ** (1.0 / m**2)
        print(f"  m={m}: ρ_m = {rho_m:.6f}")
