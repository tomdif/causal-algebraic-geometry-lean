"""
Fast d=3 gap via numba-compiled FACTORED PREFIX SUM.

The matvec factorizes: Σ_{(a',b')≤(a,b)} v = Σ_{a'≤a} [Σ_{b'≤b} v(a',b')]
Each prefix sum runs over the poset of nonincreasing functions (nf elements).

With numba: inner loops run at ~1 billion ops/sec.
For m=7: nf=1716, cost per matvec ≈ 1716² × 429 ≈ 1.3B → ~2 seconds.
vs brute force O(n²) = O(2.8M²) = 7.8T → ~500 seconds.
"""
import numpy as np
from numba import njit, prange
from scipy.sparse.linalg import LinearOperator, eigsh
import time

def enum_noninc(m):
    result = []
    def gen(prefix, max_val, remaining):
        if remaining == 0:
            result.append(tuple(prefix)); return
        for v in range(max_val + 1):
            gen(prefix + [v], v, remaining - 1)
    for first in range(m):
        gen([first], first, m - 1)
    return result

@njit(cache=True)
def build_pred_matrix(noninc_arr, nf, m):
    """Build boolean predecessor matrix: pred[i,j] = True iff noninc[j] ≤ noninc[i]."""
    pred = np.zeros((nf, nf), dtype=np.bool_)
    for i in range(nf):
        for j in range(nf):
            below = True
            for k in range(m):
                if noninc_arr[j, k] > noninc_arr[i, k]:
                    below = False
                    break
            pred[i, j] = below
    return pred

@njit(parallel=True, cache=True)
def prefix_sum_below(V_grid, pred, nf):
    """Compute G[a,b] = Σ_{b'≤b} V[a,b'] for all (a,b), then
    Y[a,b] = Σ_{a'≤a} G[a',b] for all (a,b)."""
    # Step 1: prefix sum over b for each a
    G = np.zeros((nf, nf))
    for ai in prange(nf):
        for bi in range(nf):
            total = 0.0
            for bj in range(nf):
                if pred[bi, bj]:  # bj ≤ bi
                    total += V_grid[ai, bj]
            G[ai, bi] = total

    # Step 2: prefix sum over a for each b
    Y = np.zeros((nf, nf))
    for bi in prange(nf):
        for ai in range(nf):
            total = 0.0
            for aj in range(nf):
                if pred[ai, aj]:  # aj ≤ ai
                    total += G[aj, bi]
            Y[ai, bi] = total
    return Y

@njit(parallel=True, cache=True)
def prefix_sum_above(V_grid, succ, nf):
    """Compute suffix sum: Y[a,b] = Σ_{(a',b')≥(a,b)} V[a',b']."""
    G = np.zeros((nf, nf))
    for ai in prange(nf):
        for bi in range(nf):
            total = 0.0
            for bj in range(nf):
                if succ[bi, bj]:  # bj ≥ bi
                    total += V_grid[ai, bj]
            G[ai, bi] = total

    Y = np.zeros((nf, nf))
    for bi in prange(nf):
        for ai in range(nf):
            total = 0.0
            for aj in range(nf):
                if succ[ai, aj]:  # aj ≥ ai
                    total += G[aj, bi]
            Y[ai, bi] = total
    return Y

def build_operator(m):
    """Build the fast factored operator for d=3 at grid size m."""
    t0 = time.time()
    noninc = enum_noninc(m)
    nf = len(noninc)
    noninc_arr = np.array(noninc, dtype=np.int16)

    # Build states
    states_a = []
    states_b = []
    volumes = []
    max_heights = []
    grid = -np.ones((nf, nf), dtype=np.int32)

    for ai in range(nf):
        a = noninc[ai]
        for bi in range(nf):
            b = noninc[bi]
            vol = sum(max(0, b[j] - a[j] + 1) for j in range(m))
            if vol > 0:
                idx = len(states_a)
                grid[ai, bi] = idx
                states_a.append(ai)
                states_b.append(bi)
                volumes.append(vol)
                max_heights.append(max(max(0, b[j] - a[j] + 1) for j in range(m)))

    n = len(states_a)
    state_a = np.array(states_a, dtype=np.int32)
    state_b = np.array(states_b, dtype=np.int32)
    volumes = np.array(volumes, dtype=float)
    max_heights = np.array(max_heights, dtype=float)

    t1 = time.time()

    # Build predecessor/successor matrices
    pred = build_pred_matrix(noninc_arr, nf, m)
    succ = pred.T.copy()  # succ[i,j] = True iff noninc[j] ≥ noninc[i] = pred[j,i]

    avg_pred = pred.sum() / nf
    t2 = time.time()

    print(f"  m={m}: nf={nf}, n={n}, avg_pred={avg_pred:.1f}")
    print(f"  Setup: states {t1-t0:.1f}s, DAG {t2-t1:.1f}s")

    # Warm up numba
    V_test = np.random.randn(nf, nf)
    _ = prefix_sum_below(V_test, pred, nf)
    _ = prefix_sum_above(V_test, succ, nf)
    t3 = time.time()
    print(f"  Numba warmup: {t3-t2:.1f}s")

    def matvec_sym(v):
        """(T + T^T)/2 @ v via factored prefix sums."""
        # Scatter v into nf×nf grid
        V_grid = np.zeros((nf, nf))
        for idx in range(n):
            V_grid[state_a[idx], state_b[idx]] = v[idx]

        # Below and above prefix sums
        Y_below = prefix_sum_below(V_grid, pred, nf)
        Y_above = prefix_sum_above(V_grid, succ, nf)

        # Gather results
        y = np.zeros(n)
        for idx in range(n):
            y[idx] = 0.5 * (Y_below[state_a[idx], state_b[idx]] +
                           Y_above[state_a[idx], state_b[idx]])
        return y

    return matvec_sym, n, volumes, max_heights

# ============================================================
print("=" * 70)
print("d=3 FAST GAP (numba factored prefix sum)")
print("=" * 70)

results = {}
for m in range(2, 9):
    print()
    t0 = time.time()
    mv, n, vols, mh = build_operator(m)

    # Time one matvec
    v_test = np.random.randn(n)
    t1 = time.time()
    _ = mv(v_test)
    t2 = time.time()
    mv_time = t2 - t1
    print(f"  One matvec: {mv_time:.2f}s")

    est = mv_time * 50
    if est > 7200:
        print(f"  Est. {est:.0f}s → too slow, skipping")
        continue

    A = LinearOperator((n, n), matvec=mv, dtype=float)
    t3 = time.time()
    evals, evecs = eigsh(A, k=2, which='LM', maxiter=50, tol=1e-10)
    t4 = time.time()

    idx = np.argsort(evals)[::-1]
    psi = evecs[:, idx[0]]
    if psi[n // 2] < 0: psi = -psi
    psi2 = psi**2; psi2 /= psi2.sum()

    gap_area = np.dot(psi2, vols) / m**2
    gap_maxh = np.dot(psi2, mh) / m

    print(f"  gap(area/m²) = {gap_area:.8f}")
    print(f"  gap(max_h/m) = {gap_maxh:.8f}")
    print(f"  λ₁={evals[idx[0]]:.4f}, λ₂={evals[idx[1]]:.4f}")
    print(f"  eigsh: {t4-t3:.1f}s, total: {t4-t0:.1f}s")

    results[m] = {'gap_area': gap_area, 'gap_maxh': gap_maxh, 'n': n}

if results:
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    for m_val in sorted(results):
        r = results[m_val]
        print(f"  m={m_val}: n={r['n']:>9d}, area/m²={r['gap_area']:.8f}, max_h/m={r['gap_maxh']:.8f}")

    # Extrapolation
    ms = np.array(sorted(results.keys()), dtype=float)
    gs = np.array([results[int(m)]['gap_area'] for m in ms])
    if len(ms) >= 3:
        from scipy.optimize import curve_fit
        def model(m, a, b):
            return a + b/m
        p, _ = curve_fit(model, ms, gs)
        print(f"\n  Extrapolated γ₃ = {p[0]:.6f} (from gap = {p[0]:.4f} + {p[1]:.4f}/m)")
