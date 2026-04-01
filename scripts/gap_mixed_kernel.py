"""
Comparability kernel with MIXED order on the simplex.

The slab model gives: state (lo, hi) → simplex coordinates u = lo/m, v = (m-hi)/m.
Transition: lo' ≤ lo AND hi' ≤ hi → u' ≤ u AND v' ≥ v (MIXED comparability).

So the correct kernel on {u+v ≤ 1, u,v ≥ 0} is:
K(P,Q) = 1 iff (u' ≤ u AND v' ≥ v) or (u' ≥ u AND v' ≤ v)

Gap γ = 1 - ⟨u+v⟩_ψ (since u+v = 1 - width/m).
"""

import numpy as np
from scipy.linalg import eigh
import time

def simplex_grid(d, N):
    """Grid points on d-simplex {x_i ≥ 0, Σx_i ≤ 1}."""
    if d == 1:
        return np.array([[i/N] for i in range(N+1)])
    points = []
    def gen(coords, remaining, depth):
        if depth == d - 1:
            for k in range(remaining + 1):
                points.append(coords + [k/N])
            return
        for k in range(remaining + 1):
            gen(coords + [k/N], remaining - k, depth + 1)
    gen([], N, 0)
    return np.array(points)

def compute_mixed_gap(d, N):
    """Compute gap using MIXED comparability on d-simplex."""
    points = simplex_grid(d, N)
    n = len(points)

    t0 = time.time()
    K = np.zeros((n, n), dtype=np.float32)

    for i in range(n):
        diff = points - points[i]  # (n, d)
        # Mixed comparability: coordinates alternate sign
        # For d=2: (u'≤u, v'≥v) or (u'≥u, v'≤v)
        # For d=3: need to define the "mixed" order from the slab model
        #
        # General: the slab boundaries are ALL nonincreasing (antitone in product order)
        # State = (lo_1,...,lo_{d-1}, hi_1,...,hi_{d-1}) → simplex coords
        # u_k = lo_k/m (gap at bottom of coord k+1)
        # v_k = (m - hi_k)/m (gap at top of coord k+1)
        # Transition: lo'_k ≤ lo_k → u'_k ≤ u_k
        #             hi'_k ≤ hi_k → v'_k ≥ v_k (since v = m-hi decreases when hi decreases... WAIT)
        #
        # hi' ≤ hi → m - hi' ≥ m - hi → v' ≥ v. So u decreases and v INCREASES.
        # Comparable: (u'≤u, v'≥v) or (u'≥u, v'≤v).
        #
        # For d=2 simplex: 2 coordinates (u, v). Mixed: u goes one way, v goes the other.

        if d == 2:
            # Mixed comparability: u'≤u AND v'≥v, or u'≥u AND v'≤v
            c1 = (diff[:, 0] <= 1e-10) & (diff[:, 1] >= -1e-10)
            c2 = (diff[:, 0] >= -1e-10) & (diff[:, 1] <= 1e-10)
            K[i] = (c1 | c2).astype(np.float32)
        elif d == 3:
            # For d=3: the simplex coordinates would be (u1, v1, u2, v2, ...)
            # but the d-simplex only has d coordinates.
            #
            # Actually for d=3, the "simplex" is 2D: {(u,v) : u,v ≥ 0, u+v ≤ 1}
            # representing the (lo, hi) pair rescaled. The mixed order is the same.
            # But wait, for d=3, the state is a PAIR of functions, not a single pair.
            # The simplex representation only works for d=2.
            #
            # For d=3 on the 2-simplex, we can try standard comparability as a comparison.
            c1 = (diff[:, 0] <= 1e-10) & (diff[:, 1] >= -1e-10)
            c2 = (diff[:, 0] >= -1e-10) & (diff[:, 1] <= 1e-10)
            K[i] = (c1 | c2).astype(np.float32)
        else:
            # General mixed: alternate signs? Not well-defined for d > 2
            # Just try standard comparability for comparison
            le = np.all(diff >= -1e-10, axis=1)
            ge = np.all(diff <= 1e-10, axis=1)
            K[i] = (le | ge).astype(np.float32)

    K = (K + K.T) / 2.0
    t1 = time.time()

    evals, evecs = eigh(K.astype(np.float64), subset_by_index=[n-1, n-1])
    psi = evecs[:, 0]
    psi2 = psi**2

    coord_sum = np.sum(points, axis=1)
    expected = np.dot(coord_sum, psi2) / np.sum(psi2)
    gap = 1 - expected

    t2 = time.time()
    return gap, expected, evals[0], n, t1-t0, t2-t1

# ===== d=2 with MIXED comparability =====
print("d=2, MIXED comparability on simplex")
print("=" * 60)
for N in [20, 40, 60, 80, 100, 120, 140]:
    g, exp_sum, lam, n, tb, te = compute_mixed_gap(2, N)
    print(f"  N={N:4d}, n={n:5d}: γ = {g:.8f}, ⟨u+v⟩ = {exp_sum:.8f}, λ = {lam:.2f}  "
          f"[{tb:.1f}s + {te:.1f}s]")

# Also try on the TRIANGLE {0 ≤ u ≤ w ≤ 1} with STANDARD comparability
print()
print("d=2, STANDARD comparability on triangle {0 ≤ u ≤ w ≤ 1}")
print("=" * 60)
for N in [20, 40, 60, 80, 100, 120]:
    # Generate grid on triangle {0 ≤ u ≤ w ≤ 1}
    points = []
    for i in range(N+1):
        for j in range(i, N+1):
            points.append([i/N, j/N])
    points = np.array(points)
    n = len(points)

    K = np.zeros((n, n), dtype=np.float32)
    for i in range(n):
        diff = points - points[i]
        le = np.all(diff >= -1e-10, axis=1)
        ge = np.all(diff <= 1e-10, axis=1)
        K[i] = (le | ge).astype(np.float32)
    K = (K + K.T) / 2.0

    evals, evecs = eigh(K.astype(np.float64), subset_by_index=[n-1, n-1])
    psi = evecs[:, 0]
    psi2 = psi**2

    # width/m in triangle coords: w - u
    width_frac = points[:, 1] - points[:, 0]
    avg_width = np.dot(width_frac, psi2) / np.sum(psi2)

    # u + v in simplex coords where v = 1 - w
    uv_sum = points[:, 0] + (1 - points[:, 1])
    avg_uv = np.dot(uv_sum, psi2) / np.sum(psi2)

    print(f"  N={N:4d}, n={n:5d}: ⟨w-u⟩ = {avg_width:.8f} (=width/m), "
          f"⟨u+v⟩ = {avg_uv:.8f}, γ = 1-⟨u+v⟩ = {1-avg_uv:.8f}")
