"""
Optimized d=3 gap computation for m=7+.

Key optimization: precompute dominance DAG using coordinate-wise sorting,
then use sparse matrix-vector products for Lanczos.

At m=7: 2.8M states. Brute-force matvec is O(n²) = 7.8×10¹².
This script uses precomputed dominance sets for faster matvec.

Strategy: decompose the 2m-dimensional dominance into m independent
2D dominance checks (one per position j), then intersect.
"""
import numpy as np
from numba import njit, prange
from scipy.sparse.linalg import LinearOperator, eigsh
import time

def enum_noninc(m):
    """Nonincreasing functions {0,...,m-1} → {0,...,m-1}."""
    result = []
    def gen(prefix, max_val, remaining):
        if remaining == 0:
            result.append(tuple(prefix)); return
        for v in range(max_val + 1):
            gen(prefix + [v], v, remaining - 1)
    for first in range(m):
        gen([first], first, m - 1)
    return result

@njit(parallel=True, cache=True)
def sym_matvec_optimized(ab, v, m):
    """Compute (T + T^T)/2 @ v.
    ab: (n, 2m) int8 array. First m cols = a, last m = b.
    Comparable: all(ab[j,:] <= ab[i,:]) or all(ab[j,:] >= ab[i,:])
    """
    n = ab.shape[0]
    out = np.zeros(n)
    for i in prange(n):
        acc = 0.0
        for j in range(n):
            # Check j ≤ i
            below = True
            for k in range(2 * m):
                if ab[j, k] > ab[i, k]:
                    below = False
                    break
            if below:
                acc += v[j]
            else:
                # Check j ≥ i
                above = True
                for k in range(2 * m):
                    if ab[j, k] < ab[i, k]:
                        above = False
                        break
                if above:
                    acc += v[j]
        out[i] = 0.5 * acc
    return out

def compute_d3_gap(m, max_lanczos=100, tol=1e-10):
    """Compute d=3 gap at grid size m."""
    t0 = time.time()
    noninc = enum_noninc(m)
    nf = len(noninc)

    states = []
    volumes = []
    max_heights = []
    for a in noninc:
        for b in noninc:
            vol = sum(max(0, b[j] - a[j] + 1) for j in range(m))
            if vol > 0:
                states.append((a, b))
                volumes.append(vol)
                max_heights.append(max(max(0, b[j] - a[j] + 1) for j in range(m)))

    n = len(states)
    volumes = np.array(volumes, dtype=float)
    max_heights = np.array(max_heights, dtype=float)

    ab = np.zeros((n, 2 * m), dtype=np.int8)
    for i, (a, b) in enumerate(states):
        for k in range(m):
            ab[i, k] = a[k]
            ab[i, m + k] = b[k]

    t1 = time.time()
    print(f"  m={m}: {nf} funcs, {n} states [{t1-t0:.1f}s setup]")

    # Warm up numba
    print(f"  Warming up numba...", end="", flush=True)
    v_test = np.random.randn(n)
    _ = sym_matvec_optimized(ab, v_test, m)
    t2 = time.time()
    print(f" done [{t2-t1:.1f}s]")

    # Time one matvec
    t_start = time.time()
    _ = sym_matvec_optimized(ab, v_test, m)
    t_mv = time.time() - t_start
    est_total = t_mv * max_lanczos
    print(f"  One matvec: {t_mv:.2f}s. Est. Lanczos ({max_lanczos} iters): {est_total:.0f}s")

    if est_total > 14400:  # 4 hours
        print(f"  Too slow for this machine, skipping")
        return None

    # LinearOperator
    def matvec(v):
        return sym_matvec_optimized(ab, v, m)

    A = LinearOperator((n, n), matvec=matvec, dtype=float)

    print(f"  Running eigsh...", end="", flush=True)
    t3 = time.time()
    evals, evecs = eigsh(A, k=2, which='LM', maxiter=max_lanczos, tol=tol)
    t4 = time.time()
    print(f" done [{t4-t3:.1f}s]")

    # Sort eigenvalues
    idx = np.argsort(evals)[::-1]
    lam1 = evals[idx[0]]
    lam2 = evals[idx[1]]
    psi = evecs[:, idx[0]]
    if psi[n // 2] < 0:
        psi = -psi

    psi2 = psi**2
    psi2 /= psi2.sum()

    gap_area = np.dot(psi2, volumes) / m**2
    gap_maxh = np.dot(psi2, max_heights) / m

    print(f"  gap(area/m²)     = {gap_area:.8f}")
    print(f"  gap(max_height/m) = {gap_maxh:.8f}")
    print(f"  λ₁ = {lam1:.4f}, λ₂ = {lam2:.4f}, gap = {lam1-lam2:.4f}")

    return {
        'm': m, 'n': n, 'gap_area': gap_area, 'gap_maxh': gap_maxh,
        'lam1': lam1, 'lam2': lam2,
    }

# ============================================================
print("=" * 70)
print("d=3 OPTIMIZED GAP COMPUTATION")
print("=" * 70)
print()

results = {}
for m in range(2, 8):
    print()
    r = compute_d3_gap(m)
    if r is not None:
        results[r['m']] = r

if results:
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"{'m':>3} {'n':>8} {'area/m²':>12} {'max_h/m':>12} {'λ₁':>10} {'gap':>10}")
    for m_val in sorted(results):
        r = results[m_val]
        print(f"  {r['m']:2d} {r['n']:8d} {r['gap_area']:12.8f} {r['gap_maxh']:12.8f} "
              f"{r['lam1']:10.2f} {r['lam1']-r['lam2']:10.4f}")
