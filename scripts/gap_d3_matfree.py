"""
d=3 gap computation using matrix-free Lanczos with Numba-accelerated matvec.

State = (a, b) where a, b nonincreasing {0,...,m-1} → {0,...,m-1}, a≤b somewhere.
T[i,j] = 1 iff a_j(k) ≤ a_i(k) and b_j(k) ≤ b_i(k) for all k.
T_sym = (T + T^T)/2.

Matvec: (T_sym @ v)[i] = 0.5 * sum_{j: j≤i} v[j] + 0.5 * sum_{j: j≥i} v[j]
"""
import numpy as np
from numba import njit, prange
from scipy.sparse.linalg import LinearOperator, eigsh
import time

def enum_noninc(m):
    """Enumerate nonincreasing functions {0,...,m-1} → {0,...,m-1}."""
    result = []
    def gen(prefix, max_val, remaining):
        if remaining == 0:
            result.append(tuple(prefix))
            return
        for v in range(max_val + 1):
            gen(prefix + [v], v, remaining - 1)
    for first in range(m):
        gen([first], first, m - 1)
    return result

@njit(parallel=True, cache=True)
def sym_matvec(states_ab, v):
    """Compute (T + T^T)/2 @ v using brute force with parallelization.
    states_ab: (n, 2*m) array where first m cols = a, last m cols = b.
    """
    n = states_ab.shape[0]
    m = states_ab.shape[1] // 2
    out = np.zeros(n)

    for i in prange(n):
        acc = 0.0
        a_i = states_ab[i, :m]
        b_i = states_ab[i, m:]
        for j in range(n):
            # Check j ≤ i: a_j ≤ a_i and b_j ≤ b_i
            below = True
            for k in range(m):
                if states_ab[j, k] > a_i[k] or states_ab[j, m+k] > b_i[k]:
                    below = False
                    break
            # Check j ≥ i: a_j ≥ a_i and b_j ≥ b_i
            above = True
            if not below:
                for k in range(m):
                    if states_ab[j, k] < a_i[k] or states_ab[j, m+k] < b_i[k]:
                        above = False
                        break
            if below or above:
                acc += v[j]
            elif below and above:
                acc += v[j]  # both = they're equal, count once
        out[i] = 0.5 * acc
    return out

def compute_gap_d3_matfree(m, max_iter=200, tol=1e-8):
    """Compute d=3 gap using matrix-free Lanczos."""
    t0 = time.time()

    noninc = enum_noninc(m)
    nf = len(noninc)

    # Build states
    states = []
    volumes = []
    for a in noninc:
        for b in noninc:
            vol = sum(max(0, b[j] - a[j] + 1) for j in range(m))
            if vol > 0:
                states.append((a, b))
                volumes.append(vol)

    n = len(states)
    volumes = np.array(volumes, dtype=float)

    # Pack into numpy array for numba
    states_ab = np.zeros((n, 2*m), dtype=np.int8)
    for i, (a, b) in enumerate(states):
        for k in range(m):
            states_ab[i, k] = a[k]
            states_ab[i, m+k] = b[k]

    t1 = time.time()
    print(f"  m={m}: {nf} funcs, {n} states [{t1-t0:.1f}s setup]")

    # Warm up numba
    print(f"  Warming up numba...", end="", flush=True)
    v_test = np.random.randn(n)
    _ = sym_matvec(states_ab, v_test)
    t2 = time.time()
    print(f" done [{t2-t1:.1f}s]")

    # Time one matvec
    t_start = time.time()
    _ = sym_matvec(states_ab, v_test)
    t_mv = time.time() - t_start
    print(f"  One matvec: {t_mv:.2f}s. Est. Lanczos ({max_iter} iters): {t_mv*max_iter:.0f}s")

    if t_mv * max_iter > 7200:  # 2 hours
        print(f"  Too slow, skipping")
        return None

    # LinearOperator for scipy
    def matvec(v):
        return sym_matvec(states_ab, v)

    A = LinearOperator((n, n), matvec=matvec, dtype=float)

    print(f"  Running eigsh...", end="", flush=True)
    t3 = time.time()
    evals, evecs = eigsh(A, k=1, which='LM', maxiter=max_iter, tol=tol)
    t4 = time.time()
    print(f" done [{t4-t3:.1f}s]")

    psi = evecs[:, 0]
    psi2 = psi**2
    psi2 /= psi2.sum()

    avg_vol = np.dot(psi2, volumes)
    gap = avg_vol / m**2

    # Max height
    max_heights = np.array([max(max(0, b[j] - a[j] + 1) for j in range(m))
                           for a, b in states], dtype=float)
    avg_max_h = np.dot(psi2, max_heights) / m

    print(f"  gap(area/m²) = {gap:.8f}")
    print(f"  ⟨max_height/m⟩ = {avg_max_h:.8f}")
    print(f"  λ = {evals[0]:.4f}")

    return gap

print("=" * 60)
print("d=3 gap: matrix-free Lanczos with Numba matvec")
print("=" * 60)

results = {}
for m in range(2, 8):
    print()
    g = compute_gap_d3_matfree(m)
    if g is not None:
        results[m] = g
    else:
        break

# Extrapolation
print("\n" + "=" * 60)
print("Results summary")
print("=" * 60)
for m, g in results.items():
    print(f"  m={m}: gap = {g:.8f}")

if len(results) >= 3:
    from numpy.linalg import lstsq
    ms = np.array(list(results.keys()), dtype=float)
    gs = np.array(list(results.values()))
    # Fit gap(m) = γ + a/m + b/m²
    A = np.column_stack([np.ones(len(ms)), 1/ms, 1/ms**2])
    coeff = lstsq(A, gs, rcond=None)[0]
    print(f"\n  Extrapolated γ₃(∞) = {coeff[0]:.8f}")
    print(f"  (fit: γ + {coeff[1]:.4f}/m + {coeff[2]:.4f}/m²)")
