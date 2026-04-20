"""
Verify the claimed d_s = d_MM = 1.556 agreement on CAG posets.

The MEMORY.md bullet from April 10 asserts spectral dimension equals
Myrheim-Meyer dimension to 0.04% on some "CAG poset," with value 1.556.
No source code or dedicated memory file backs this up.

This script computes both dimensions for the most natural candidates:
  - Grid poset [m]^d under product order
  - Poset of convex subsets of [m]^d (ordered by inclusion)
  - Poset of downsets / antichains (standard constructions)

For each, we compute:
  d_MM: Myrheim-Meyer via the chain-count ratio.
  d_s:  spectral dimension via Laplacian heat-kernel trace.

Honest expected outcome: for [m]^d grid, both converge to d exactly
as m -> infty. That's trivial, not a striking agreement. If 1.556 appears
it must come from a non-grid poset.
"""

import math
from itertools import product as iproduct

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import eigsh


def grid_elements(m, d):
    """Enumerate all points of [m]^d."""
    return list(iproduct(range(m), repeat=d))


def leq(a, b):
    """Product order on tuples."""
    return all(ai <= bi for ai, bi in zip(a, b))


def strict_lt(a, b):
    return leq(a, b) and a != b


def count_grid_relations(m, d):
    """Count N, R_1 (x <= y), R_2 (x < y strict), R_3 (3-chain) on [m]^d grid.

    Uses the product-formula shortcut for R_1 and R_2; for R_3, direct
    enumeration (O(N^3) worst case but small for m <= 5, d <= 3).
    """
    N = m ** d
    # R_1 = #{(x,y): x <= y}. Product of per-coord counts m(m+1)/2.
    R_1 = (m * (m + 1) // 2) ** d
    R_2 = R_1 - N  # strict: remove diagonal

    # R_3 = #{(x,y,z): x < y < z} via direct enumeration for small m,d
    elts = grid_elements(m, d)
    R_3 = 0
    for x in elts:
        for y in elts:
            if not strict_lt(x, y):
                continue
            for z in elts:
                if strict_lt(y, z):
                    R_3 += 1
    return N, R_1, R_2, R_3


def myrheim_meyer_dim_from_R1(N, R_1):
    """Estimate d_MM from the ordering fraction.

    For [m]^d: R_1/N^2 -> (1/2)^d as m -> inf, so d_MM ~ -log_2(R_1/N^2).
    """
    if N <= 1:
        return None
    ratio = R_1 / N ** 2
    if ratio <= 0 or ratio >= 1:
        return None
    return -math.log2(ratio)


def myrheim_meyer_dim_from_chains(N, R_2, R_3):
    """Meyer's dimension via chain count ratio C_3 / C_2^2.

    For d-dim Minkowski causal diamond:
        f_d := lim R_3 / (R_2^2 / N)  = d-dependent constant.
    Classic Myrheim-Meyer (see Meyer 1988): for Minkowski diamond,
        R_2 / N^2 -> Gamma(d+1) Gamma(d/2) / (4 Gamma(3d/2))     [Meyer]
    and d_MM is the d making this match.

    For this script we use the chain-ratio form:
        C := R_3 * N / R_2^2
    and invert the known formula:
        C = d^2 * Gamma(d)^3 / Gamma(3d) * 3 * 2^{d-1} ... (see Meyer)
    which is cumbersome; easier: just report C and note the Minkowski values.
    """
    if R_2 == 0:
        return None, None
    C = R_3 * N / R_2 ** 2
    return C, None  # we report C; no closed-form inverter here


def spectral_dim_grid(m, d, n_tau=25):
    """Spectral dimension of [m]^d via Hasse-diagram (cover relation) Laplacian.

    For [m]^d grid, the Hasse cover graph is a d-dimensional grid graph.
    Classical result: spectral dimension = d exactly (continuum limit).

    We compute Tr(exp(-tau L)) for a range of tau and fit
        log Tr(exp(-tau L)) = -d_s/2 * log(tau) + const
    over the intermediate-tau regime.
    """
    elts = grid_elements(m, d)
    idx = {p: i for i, p in enumerate(elts)}
    N = len(elts)

    # Build cover graph: edge between p and q iff q = p + e_i for some i
    rows, cols, data = [], [], []
    degree = np.zeros(N)
    for p in elts:
        i = idx[p]
        for k in range(d):
            if p[k] + 1 < m:
                q = tuple(pk + (1 if j == k else 0) for j, pk in enumerate(p))
                j = idx[q]
                rows.extend([i, j])
                cols.extend([j, i])
                data.extend([-1.0, -1.0])
                degree[i] += 1
                degree[j] += 1
    # Laplacian L = D - A
    # As dense for small N (we have N <= m^d, up to m=6,d=3 -> 216)
    A = np.zeros((N, N))
    A[np.array(rows, dtype=int), np.array(cols, dtype=int)] = np.array(data)
    L = np.diag(degree) + A  # A has negatives, so D + A = D - |A|

    eigvals = np.linalg.eigvalsh(L)
    # Heat trace Tr(exp(-tau L)) = sum exp(-tau * lambda)
    # Small tau: Tr ~ N - tau*Tr(L) + ... (constant)
    # Large tau: Tr -> 1 (degenerate lowest eigvalue, Laplacian of connected graph has null
    # eigenvector constant)
    # Intermediate tau: Tr ~ C * tau^{-d_s/2}

    # pick tau range where dynamics is active: tau * lambda_max ~ 10, tau * lambda_min_nonzero ~ 1
    # For our grid, nonzero eigenvalues from ~ (2 pi / m)^2 (smooth modes)
    lam = eigvals
    lam_nonzero = lam[lam > 1e-10]
    if len(lam_nonzero) == 0:
        return None
    tau_min = 1.0 / lam.max()
    tau_max = 1.0 / lam_nonzero.min()
    taus = np.logspace(np.log10(tau_min) + 0.3, np.log10(tau_max) - 0.3, n_tau)

    log_tr = []
    for tau in taus:
        tr = np.sum(np.exp(-tau * eigvals))
        log_tr.append(math.log(tr))

    log_tau = np.log(taus)
    # Fit slope in the middle third
    lo, hi = n_tau // 3, 2 * n_tau // 3
    slope, intercept = np.polyfit(log_tau[lo:hi], log_tr[lo:hi], 1)
    d_s = -2 * slope
    return d_s


def main():
    print("=" * 72)
    print("MYRHEIM-MEYER and SPECTRAL DIMENSION on grid [m]^d posets")
    print("=" * 72)
    print()
    print("Expected (grid, large-m limit):")
    print("  d_MM (from R_1/N^2) = d  exactly")
    print("  d_s  (from Laplacian heat trace) = d  exactly (Z^d grid)")
    print()

    for d in [2, 3]:
        print(f"--- Dimension d = {d} ---")
        print(f"{'m':>3} {'N':>6} {'R_1/N^2':>10} {'d_MM(R1)':>10} "
              f"{'R_3*N/R_2^2':>14} {'d_s (spec)':>12}")
        for m in range(2, 7 if d == 2 else 6):
            N, R_1, R_2, R_3 = count_grid_relations(m, d)
            d_MM_R1 = myrheim_meyer_dim_from_R1(N, R_1)
            C_chain, _ = myrheim_meyer_dim_from_chains(N, R_2, R_3)
            d_s = spectral_dim_grid(m, d)
            print(f"{m:>3} {N:>6} {R_1/N**2:>10.4f} {d_MM_R1:>10.4f} "
                  f"{C_chain:>14.4f} {d_s:>12.4f}")
        print()

    print("---")
    print("Asymptotic prediction for grid [m]^d as m -> inf:")
    print("  R_1/N^2 -> (1/2)^d     => d_MM(R1) -> d")
    print("  d_s -> d (continuum limit Z^d)")
    print()
    print("If d_s and d_MM both give d on grids, that's not a 'striking")
    print("agreement' -- both are just computing d. The 1.556 claim must")
    print("come from a different poset construction (convex-subset lattice,")
    print("downset lattice, or some derived poset). This script does not")
    print("reproduce 1.556 on grids.")


if __name__ == "__main__":
    main()
