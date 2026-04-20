"""
Test spectral dimension on the COMPARABILITY graph of [m]^d
(not the cover/Hasse graph).

The comparability graph has an edge between x and y whenever x <= y OR y <= x,
for x != y. This is denser than the Hasse cover graph and is the natural
object for causal-set computations. Its Laplacian heat kernel gives a
different spectral dimension that may match Myrheim-Meyer on the same poset.

If d_s (comparability) agrees with d_MM, the April 10 memory claim
  "d_s = d_MM = 1.556 to 0.04% on CAG poset"
is plausibly reproduced on a grid poset at a specific (m, d).
"""

import math
from itertools import product as iproduct

import numpy as np


def grid_elements(m, d):
    return list(iproduct(range(m), repeat=d))


def leq(a, b):
    return all(ai <= bi for ai, bi in zip(a, b))


def comparability_laplacian(m, d):
    """Graph Laplacian L = D - A for the comparability graph on [m]^d.

    Edge between x, y iff they are comparable (x <= y or y <= x), x != y.
    """
    elts = grid_elements(m, d)
    N = len(elts)
    A = np.zeros((N, N))
    for i, x in enumerate(elts):
        for j, y in enumerate(elts):
            if i == j:
                continue
            if leq(x, y) or leq(y, x):
                A[i, j] = 1
    degree = A.sum(axis=1)
    L = np.diag(degree) - A
    return L


def spectral_dim_from_laplacian(L, n_tau=30):
    """Compute d_s from heat trace Tr(exp(-tau L)).

    Return d_s and the quality indicator (R^2 of the linear fit).
    """
    eigvals = np.linalg.eigvalsh(L)
    lam = eigvals
    lam_nonzero = lam[lam > 1e-9]
    if len(lam_nonzero) == 0:
        return None, None
    tau_min = 1.0 / lam.max()
    tau_max = 1.0 / lam_nonzero.min()
    # mid-range: avoid both small-tau (counts N, no dim info) and large-tau (-> 1)
    taus = np.logspace(
        np.log10(tau_min) + 0.5, np.log10(tau_max) - 0.5, n_tau
    )
    log_tr = np.array(
        [math.log(np.sum(np.exp(-tau * eigvals))) for tau in taus]
    )
    log_tau = np.log(taus)
    # Fit on middle third
    lo, hi = n_tau // 3, 2 * n_tau // 3
    slope, intercept = np.polyfit(log_tau[lo:hi], log_tr[lo:hi], 1)
    # R^2
    pred = slope * log_tau[lo:hi] + intercept
    ss_res = np.sum((log_tr[lo:hi] - pred) ** 2)
    ss_tot = np.sum((log_tr[lo:hi] - log_tr[lo:hi].mean()) ** 2)
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0
    return -2 * slope, r2


def myrheim_meyer_from_R1(m, d):
    N = m ** d
    R_1 = (m * (m + 1) // 2) ** d
    return -math.log2(R_1 / N ** 2)


def main():
    print("=" * 78)
    print("COMPARABILITY-GRAPH spectral dimension vs Myrheim-Meyer on [m]^d")
    print("=" * 78)
    print()
    print("d_s computed from Laplacian of FULL comparability graph (not cover).")
    print("d_MM computed from R_1/N^2 = [(m+1)/(2m)]^d -> (1/2)^d.")
    print()
    header = f"{'d':>2} {'m':>3} {'N':>5} {'d_MM':>8} {'d_s(cmp)':>10} " \
             f"{'|diff|':>8} {'rel %':>8} {'R^2':>7}"
    print(header)
    print("-" * len(header))

    # Small cases only (dense Laplacian)
    configs = []
    for d in [2, 3]:
        for m in range(2, 8 if d == 2 else 6):
            configs.append((d, m))

    for d, m in configs:
        N = m ** d
        if N > 300:
            continue
        d_MM = myrheim_meyer_from_R1(m, d)
        L = comparability_laplacian(m, d)
        d_s, r2 = spectral_dim_from_laplacian(L)
        diff = abs(d_s - d_MM)
        rel_pct = 100 * diff / d_MM
        print(f"{d:>2} {m:>3} {N:>5} {d_MM:>8.4f} {d_s:>10.4f} "
              f"{diff:>8.4f} {rel_pct:>7.3f}% {r2:>7.4f}")


if __name__ == "__main__":
    main()
