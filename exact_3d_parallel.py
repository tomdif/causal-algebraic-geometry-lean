"""
Parallelized exact |CC([m]³)| using multiprocessing + C + uint128.

The inner loop over target configs c is embarrassingly parallel.
Each worker handles a chunk of target configs.
"""

import numpy as np
import ctypes
import time
import os
from multiprocessing import Pool, shared_memory

_dir = os.path.dirname(os.path.abspath(__file__))
SO_PATH = os.path.join(_dir, 'compat_check.so')


def _load_lib():
    lib = ctypes.CDLL(SO_PATH)
    lib.sum_compatible_128.restype = None
    lib.sum_compatible_128.argtypes = [
        ctypes.POINTER(ctypes.c_int),
        ctypes.POINTER(ctypes.c_int),
        ctypes.POINTER(ctypes.c_int),
        ctypes.POINTER(ctypes.c_uint64),
        ctypes.POINTER(ctypes.c_uint64),
        ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
        ctypes.POINTER(ctypes.c_uint64),
        ctypes.POINTER(ctypes.c_uint64),
    ]
    return lib


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


MASK64 = (1 << 64) - 1


def to_hilo(n):
    return (n >> 64) & MASK64, n & MASK64


def from_hilo(hi, lo):
    return (int(hi) << 64) | int(lo)


# Global state for workers (set once per worker via initializer)
_worker_state = {}


def _worker_init(configs_flat_bytes, n, m):
    """Initialize worker with config data."""
    global _worker_state
    lib = _load_lib()
    configs_flat = np.frombuffer(configs_flat_bytes, dtype=np.int32).copy()
    _worker_state['lib'] = lib
    _worker_state['configs_flat'] = configs_flat
    _worker_state['configs_ptr'] = configs_flat.ctypes.data_as(
        ctypes.POINTER(ctypes.c_int))
    _worker_state['n'] = n
    _worker_state['m'] = m


def _worker_process_chunk(args):
    """Process a chunk of target configs c, return list of (c, contrib_hi, contrib_lo).

    args: (c_list, dp_adj_hi_bytes, dp_adj_lo_bytes, dp_gap_hi_bytes, dp_gap_lo_bytes,
           dp_none_hi, dp_none_lo, empty_idx)
    """
    (c_list, dp_adj_hi_b, dp_adj_lo_b, dp_gap_hi_b, dp_gap_lo_b,
     dp_none_hi, dp_none_lo, empty_idx) = args

    lib = _worker_state['lib']
    configs_flat = _worker_state['configs_flat']
    configs_ptr = _worker_state['configs_ptr']
    n = _worker_state['n']
    m = _worker_state['m']

    dp_adj_hi = np.frombuffer(dp_adj_hi_b, dtype=np.uint64).copy()
    dp_adj_lo = np.frombuffer(dp_adj_lo_b, dtype=np.uint64).copy()
    dp_gap_hi = np.frombuffer(dp_gap_hi_b, dtype=np.uint64).copy()
    dp_gap_lo = np.frombuffer(dp_gap_lo_b, dtype=np.uint64).copy()

    dp_adj_hi_ptr = dp_adj_hi.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64))
    dp_adj_lo_ptr = dp_adj_lo.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64))
    dp_gap_hi_ptr = dp_gap_hi.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64))
    dp_gap_lo_ptr = dp_gap_lo.ctypes.data_as(ctypes.POINTER(ctypes.c_uint64))

    dp_none = from_hilo(dp_none_hi, dp_none_lo)

    out_hi = ctypes.c_uint64(0)
    out_lo = ctypes.c_uint64(0)

    results = []
    for c in c_list:
        if c == empty_idx:
            results.append((c, 0, 0))
            continue

        L_c = configs_flat[c * 2 * m: c * 2 * m + m]
        U_c = configs_flat[c * 2 * m + m: c * 2 * m + 2 * m]
        L_c_ptr = L_c.ctypes.data_as(ctypes.POINTER(ctypes.c_int))
        U_c_ptr = U_c.ctypes.data_as(ctypes.POINTER(ctypes.c_int))

        contrib = dp_none

        lib.sum_compatible_128(L_c_ptr, U_c_ptr, configs_ptr,
                                dp_adj_hi_ptr, dp_adj_lo_ptr,
                                n, m, 0, empty_idx,
                                ctypes.byref(out_hi), ctypes.byref(out_lo))
        contrib += from_hilo(out_hi.value, out_lo.value)

        lib.sum_compatible_128(L_c_ptr, U_c_ptr, configs_ptr,
                                dp_gap_hi_ptr, dp_gap_lo_ptr,
                                n, m, 1, empty_idx,
                                ctypes.byref(out_hi), ctypes.byref(out_lo))
        contrib += from_hilo(out_hi.value, out_lo.value)

        hi, lo = to_hilo(contrib)
        results.append((c, hi, lo))

    return results


def exact_count_3d_parallel(m, n_workers=None):
    if n_workers is None:
        n_workers = os.cpu_count() or 4

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

    configs_flat = np.zeros(n * 2 * m, dtype=np.int32)
    for i, (L, U) in enumerate(configs):
        for j in range(m):
            configs_flat[i * 2 * m + j] = L[j]
            configs_flat[i * 2 * m + m + j] = U[j]
    configs_flat_bytes = configs_flat.tobytes()

    # DP arrays
    dp_adj_hi = np.zeros(n, dtype=np.uint64)
    dp_adj_lo = np.zeros(n, dtype=np.uint64)
    dp_gap_hi = np.zeros(n, dtype=np.uint64)
    dp_gap_lo = np.zeros(n, dtype=np.uint64)
    dp_none = 0

    for c in range(n):
        if c == empty_idx:
            dp_none += 1
        else:
            dp_adj_lo[c] = 1

    print(f"  Using {n_workers} worker processes")

    with Pool(n_workers,
              initializer=_worker_init,
              initargs=(configs_flat_bytes, n, m)) as pool:

        for layer in range(1, m):
            t1 = time.time()
            new_adj_hi = np.zeros(n, dtype=np.uint64)
            new_adj_lo = np.zeros(n, dtype=np.uint64)
            new_gap_hi = np.zeros(n, dtype=np.uint64)
            new_gap_lo = np.zeros(n, dtype=np.uint64)
            new_none = dp_none

            # Empty transitions
            for i in range(n):
                if i == empty_idx:
                    continue
                val = (from_hilo(dp_adj_hi[i], dp_adj_lo[i]) +
                       from_hilo(dp_gap_hi[i], dp_gap_lo[i]))
                hi, lo = to_hilo(val)
                new_gap_hi[i] = hi
                new_gap_lo[i] = lo

            # Parallel: split target configs into chunks
            chunk_size = max(100, n // (n_workers * 4))
            c_chunks = [list(range(i, min(i + chunk_size, n)))
                        for i in range(0, n, chunk_size)]

            dp_none_hi, dp_none_lo = to_hilo(dp_none)
            tasks = [
                (c_chunk,
                 dp_adj_hi.tobytes(), dp_adj_lo.tobytes(),
                 dp_gap_hi.tobytes(), dp_gap_lo.tobytes(),
                 dp_none_hi, dp_none_lo, empty_idx)
                for c_chunk in c_chunks
            ]

            print(f"    layer {layer+1}/{m} ({len(c_chunks)} chunks)...",
                  end=" ", flush=True)

            for chunk_result in pool.imap_unordered(_worker_process_chunk, tasks):
                for (c, hi, lo) in chunk_result:
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
        total += from_hilo(dp_adj_hi[i], dp_adj_lo[i])
        total += from_hilo(dp_gap_hi[i], dp_gap_lo[i])
    return total


if __name__ == '__main__':
    from math import log

    known = {2: 101, 3: 129535, 4: 4664028094, 5: 4725549877891433}

    # Verify
    for m in [2, 3, 4]:
        print(f"\nm={m}:")
        c = exact_count_3d_parallel(m)
        match = "✓" if c == known[m] else f"✗ (got {c})"
        print(f"  |CC([{m}]³)| = {c} {match}")

    # m=5 timing
    print(f"\nm=5 (parallel):")
    t0 = time.time()
    c5 = exact_count_3d_parallel(5)
    dt = time.time() - t0
    match = "✓" if c5 == known[5] else f"✗ (got {c5})"
    print(f"  |CC([5]³)| = {c5} {match} ({dt:.1f}s)")

    # m=6
    print(f"\nm=6 (parallel):")
    t0 = time.time()
    c6 = exact_count_3d_parallel(6)
    dt = time.time() - t0
    rho = c6 ** (1.0 / 36)
    print(f"  |CC([6]³)| = {c6}")
    print(f"  |CC|^{{1/36}} = {rho:.6f}")
    print(f"  Time: {dt:.1f}s")

    # Fit analysis
    vals = dict(known)
    vals[6] = c6
    ms = np.array([2, 3, 4, 5, 6], dtype=float)
    log_cc = np.array([log(vals[m]) for m in [2, 3, 4, 5, 6]])

    print("\n=== FIT ANALYSIS ===\n")
    A1 = np.vstack([ms**2, ms, np.ones(5)]).T
    c1 = np.linalg.lstsq(A1, log_cc, rcond=None)[0]
    resid1 = log_cc - A1 @ c1
    print(f"Quadratic: log|CC| = {c1[0]:.6f}·m² + {c1[1]:.6f}·m + {c1[2]:.4f}")
    print(f"  ρ₃ = {np.exp(c1[0]):.6f}, β₃ = {-c1[1]:.6f}, RSS = {np.sum(resid1**2):.2e}")

    A2 = np.vstack([ms**2, ms, np.log(ms), np.ones(5)]).T
    c2 = np.linalg.lstsq(A2, log_cc, rcond=None)[0]
    resid2 = log_cc - A2 @ c2
    print(f"\nWith log(m): {c2[0]:.6f}·m² + {c2[1]:.6f}·m + {c2[2]:.4f}·log(m) + {c2[3]:.4f}")
    print(f"  ρ₃ = {np.exp(c2[0]):.6f}")
    print(f"  Coefficient of log(m): {c2[2]:.6f}")
    print(f"  RSS = {np.sum(resid2**2):.2e}")
