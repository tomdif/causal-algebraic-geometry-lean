"""
Narrow first experiment: apply a chamber-style reflection construction to
the divisor lattice with the natural arithmetic involution n <-> N/n.

Does not attempt to reproduce RH; just probes whether the chamber machinery
has anything to say about the divisor lattice's spectrum.

Setup:
  - Fix N with small number of distinct primes P and bounded exponents.
  - Divisors d | N form a product-of-chains poset.
  - Define comparability kernel K(d, d') = 1 if d | d' or d' | d else 0.
  - Involution R(d) = N/d is a Z/2 action on divisors.
  - "Antisymmetric" sector: functions f on divisors with f(d) = -f(N/d).
  - Restrict K to the antisymmetric sector.
  - Check spectrum of K_anti and compare with zeros of the truncated
    Dirichlet polynomial zeta_P(s) = prod_{p <= P} (1 - p^{-s})^{-1} near
    the critical line.
"""
import math
import numpy as np


def divisors(N):
    ds = []
    i = 1
    while i * i <= N:
        if N % i == 0:
            ds.append(i)
            if i * i != N:
                ds.append(N // i)
        i += 1
    return sorted(ds)


def comparability_kernel(divs):
    n = len(divs)
    K = np.zeros((n, n))
    for i, a in enumerate(divs):
        for j, b in enumerate(divs):
            if i == j or (b % a == 0) or (a % b == 0):
                K[i, j] = 1.0
    return K


def involution_matrix(divs, N):
    n = len(divs)
    idx = {d: i for i, d in enumerate(divs)}
    R = np.zeros((n, n))
    for i, d in enumerate(divs):
        j = idx[N // d]
        R[i, j] = 1.0
    return R


def project_antisymmetric(K, R):
    # Antisymmetric: f with Rf = -f, i.e., (I + R) f = 0.
    # So we restrict K to eigenspace of R with eigenvalue -1.
    # Find basis for -1 eigenspace of R.
    evals, evecs = np.linalg.eigh(R)
    mask = np.abs(evals + 1) < 1e-8
    V = evecs[:, mask]  # basis for the -1 eigenspace
    K_anti = V.T @ K @ V
    return K_anti, V.shape[1]


def main():
    for N in [6, 30, 210, 2310]:
        divs = divisors(N)
        n = len(divs)
        K = comparability_kernel(divs)
        R = involution_matrix(divs, N)
        # R should be an involution
        assert np.allclose(R @ R, np.eye(n))
        # R should have eigenvalues +1 and -1
        evals_R, _ = np.linalg.eigh(R)
        n_pos = int(np.sum(np.abs(evals_R - 1) < 1e-8))
        n_neg = int(np.sum(np.abs(evals_R + 1) < 1e-8))

        K_anti, dim_anti = project_antisymmetric(K, R)
        spec_anti = np.linalg.eigvalsh(K_anti)
        spec_full = np.linalg.eigvalsh(K)

        print(f"N = {N}: {n} divisors, involution has {n_pos} fixed + {n_neg} anti")
        print(f"  K full spectrum range: [{spec_full.min():.4f}, {spec_full.max():.4f}]")
        print(f"  K anti-sector spectrum range: "
              f"[{spec_anti.min():.4f}, {spec_anti.max():.4f}]")
        print(f"  K anti-sector spectrum: "
              f"{np.sort(spec_anti)[:10]}{'...' if len(spec_anti) > 10 else ''}")

        # For N = prod of first P primes (squarefree case), divisors biject
        # with subsets of primes. Check signatures at squarefree N.
        # Also compute trace of K_anti (sum of eigenvalues) — zero for any
        # symmetric kernel on anti-sector of a perfect involution.
        print(f"  trace K_anti = {np.trace(K_anti):.4f}")
        print(f"  sum |spec| = {np.sum(np.abs(spec_anti)):.4f}")
        print()


if __name__ == "__main__":
    main()
