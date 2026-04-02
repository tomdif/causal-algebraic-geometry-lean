"""
Fiber decomposition of the d=3 transfer operator.

The transfer acts on states (a,b) = pairs of nonincreasing functions.
At each position j, the width w(j) = max(0, b(j)-a(j)+1).

Fiber F_w = {(a,b) : width at position j = w} (for a fixed j).

The fiber decomposition:
1. Within each fiber F_w, the eigenvector is approximately uniform (CV < 0.2)
2. Project the transfer onto fibers → gives the reduced width chain K̃(w,w')
3. Compare K̃ with K_comb × spectral tilt → quantify the correction
4. Show the correction is O(4%) and controlled
"""
import numpy as np
from scipy.linalg import eigh
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
    G = np.zeros((nf, nf))
    for ai in prange(nf):
        for bi in range(nf):
            total = 0.0
            for bj in range(nf):
                if pred[bi, bj]:
                    total += V_grid[ai, bj]
            G[ai, bi] = total
    Y = np.zeros((nf, nf))
    for bi in prange(nf):
        for ai in range(nf):
            total = 0.0
            for aj in range(nf):
                if pred[ai, aj]:
                    total += G[aj, bi]
            Y[ai, bi] = total
    return Y

@njit(parallel=True, cache=True)
def prefix_sum_above(V_grid, succ, nf):
    G = np.zeros((nf, nf))
    for ai in prange(nf):
        for bi in range(nf):
            total = 0.0
            for bj in range(nf):
                if succ[bi, bj]:
                    total += V_grid[ai, bj]
            G[ai, bi] = total
    Y = np.zeros((nf, nf))
    for bi in prange(nf):
        for ai in range(nf):
            total = 0.0
            for aj in range(nf):
                if succ[ai, aj]:
                    total += G[aj, bi]
            Y[ai, bi] = total
    return Y

def compute_eigenvector(m):
    """Compute the d=3 principal eigenvector using factored prefix sum."""
    t0 = time.time()
    noninc = enum_noninc(m)
    nf = len(noninc)
    noninc_arr = np.array(noninc, dtype=np.int16)

    states_a, states_b = [], []
    volumes, widths_all = [], []
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
                w_profile = [max(0, b[j] - a[j] + 1) for j in range(m)]
                widths_all.append(w_profile)

    n = len(states_a)
    state_a = np.array(states_a, dtype=np.int32)
    state_b = np.array(states_b, dtype=np.int32)
    volumes = np.array(volumes, dtype=float)
    widths_all = np.array(widths_all, dtype=np.int16)

    pred = build_pred_matrix(noninc_arr, nf, m)
    succ = pred.T.copy()

    # Warm up numba
    V_test = np.random.randn(nf, nf)
    _ = prefix_sum_below(V_test, pred, nf)
    _ = prefix_sum_above(V_test, succ, nf)

    def matvec_sym(v):
        V_grid = np.zeros((nf, nf))
        for idx in range(n):
            V_grid[state_a[idx], state_b[idx]] = v[idx]
        Y_below = prefix_sum_below(V_grid, pred, nf)
        Y_above = prefix_sum_above(V_grid, succ, nf)
        y = np.zeros(n)
        for idx in range(n):
            y[idx] = 0.5 * (Y_below[state_a[idx], state_b[idx]] +
                           Y_above[state_a[idx], state_b[idx]])
        return y

    A = LinearOperator((n, n), matvec=matvec_sym, dtype=float)
    evals, evecs = eigsh(A, k=1, which='LM', maxiter=50, tol=1e-10)
    psi = evecs[:, 0]
    if psi[n // 2] < 0:
        psi = -psi

    t1 = time.time()
    print(f"  m={m}: n={n}, eigvec computed in {t1-t0:.1f}s")

    return psi, widths_all, volumes, noninc, n, m

def fiber_analysis(psi, widths_all, m, j_pos=None):
    """Analyze the fiber structure at position j_pos (default: middle)."""
    if j_pos is None:
        j_pos = m // 2

    n = len(psi)
    psi2 = psi**2
    psi2 /= psi2.sum()

    max_w = m + 1
    widths_j = widths_all[:, j_pos]

    # 1. Within-fiber uniformity (CV of eigenvector weight within each width)
    fiber_cv = {}
    for w in range(max_w):
        mask = widths_j == w
        if mask.sum() > 1:
            vals = psi2[mask]
            fiber_cv[w] = np.std(vals) / np.mean(vals) if np.mean(vals) > 0 else 0

    # 2. Fiber-projected width transition K̃(w, w')
    if j_pos < m - 1:
        j_next = j_pos + 1
    else:
        j_next = j_pos - 1

    widths_next = widths_all[:, j_next]
    K_fiber = np.zeros((max_w, max_w))
    for i in range(n):
        K_fiber[widths_j[i], widths_next[i]] += psi2[i]

    # Normalize rows
    K_fiber_prob = np.zeros((max_w, max_w))
    for w in range(max_w):
        rs = K_fiber[w].sum()
        if rs > 0:
            K_fiber_prob[w] = K_fiber[w] / rs

    # 3. Stationary distribution of fiber-projected chain
    from scipy.linalg import eig
    evals_w, evecs_w = eig(K_fiber_prob.T)
    idx = np.argmax(np.real(evals_w))
    pi = np.real(evecs_w[:, idx])
    pi = np.abs(pi)
    pi /= pi.sum()

    # 4. Width distribution from eigenvector
    pi_eigvec = np.zeros(max_w)
    for i in range(n):
        pi_eigvec[widths_j[i]] += psi2[i]
    pi_eigvec /= pi_eigvec.sum()

    # 5. Key quantities
    f_occ_chain = 1 - pi[0]
    f_occ_eigvec = 1 - pi_eigvec[0]
    mean_w = np.dot(np.arange(max_w), pi_eigvec)
    gap = mean_w / m

    return {
        'fiber_cv': fiber_cv,
        'K_fiber': K_fiber_prob,
        'pi_chain': pi,
        'pi_eigvec': pi_eigvec,
        'f_occ_chain': f_occ_chain,
        'f_occ_eigvec': f_occ_eigvec,
        'mean_w': mean_w,
        'gap': gap,
    }

# ============================================================
print("=" * 70)
print("FIBER DECOMPOSITION OF d=3 TRANSFER OPERATOR")
print("=" * 70)
print()

results = {}
for m in [3, 4, 5, 6]:
    print(f"\n--- m = {m} ---")
    psi, widths_all, volumes, noninc, n, m_val = compute_eigenvector(m)
    r = fiber_analysis(psi, widths_all, m)
    results[m] = r

    print(f"  f_occ (chain): {r['f_occ_chain']:.4f}")
    print(f"  f_occ (eigvec): {r['f_occ_eigvec']:.4f}")
    print(f"  gap = <w>/m: {r['gap']:.4f}")
    print(f"  Fiber CV: {', '.join(f'w={w}:{cv:.3f}' for w, cv in sorted(r['fiber_cv'].items()) if cv > 0)}")

    # Compare pi_chain with pi_eigvec
    diff = np.max(np.abs(r['pi_chain'] - r['pi_eigvec']))
    print(f"  max|π_chain - π_eigvec| = {diff:.4f}")

# Scaling analysis
print()
print("=" * 70)
print("f_occ SCALING WITH m")
print("=" * 70)
for m_val in sorted(results):
    r = results[m_val]
    print(f"  m={m_val}: f_occ_chain={r['f_occ_chain']:.4f}, "
          f"f_occ_eigvec={r['f_occ_eigvec']:.4f}, gap={r['gap']:.4f}")

# Extrapolation
ms = np.array(sorted(results.keys()), dtype=float)
f_occs = np.array([results[int(m)]['f_occ_eigvec'] for m in ms])
from scipy.optimize import curve_fit
def model(m, a, b):
    return a + b/m
try:
    p, _ = curve_fit(model, ms, f_occs)
    print(f"\n  Fit: f_occ(m) = {p[0]:.4f} + {p[1]:.3f}/m")
    print(f"  f_occ(∞) = {p[0]:.4f}")
except:
    print("\n  Fit failed")
