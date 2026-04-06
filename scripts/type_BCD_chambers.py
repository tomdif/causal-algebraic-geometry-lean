#!/usr/bin/env python3
"""
Type B, C, D Root System Chamber Kernels — v2
==============================================

The correct construction:

TYPE A_n:
  - Full lattice: [m]^n = {0,...,m-1}^n
  - Kernel: K(x,y) = 1 if x <= y or y <= x (comparability in product order)
  - Group: S_n acts by permuting coordinates
  - Chamber: {x_1 < x_2 < ... < x_n}
  - Chamber kernel: K_F(P,Q) = sum_{sigma} sgn(sigma) K(P, sigma(Q))
  - Eigenvalue ratio: le_even / lo_odd -> (d+1)/(d-1) as m -> inf

TYPE B_n:
  - Full lattice: {-m,...,-1,0,1,...,m}^n  (or {-(m-1),...,m-1}^n)
  - Kernel: K(x,y) = 1 if x <= y or y <= x (componentwise)
  - Group: B_n = signed permutations (permute coords AND flip signs)
  - Chamber: {0 < x_1 < x_2 < ... < x_n} (strict positivity)

TYPE D_n:
  - Same lattice as B_n
  - Group: D_n = even signed permutations (even number of sign flips)
  - Chamber: {0 < x_1 < x_2 < ... < x_n} with |x_1| constraint handled by group

The KEY INSIGHT from the Type A analysis:
  The eigenvalue ratio comes from the COMPOUND VOLTERRA SVD mechanism.
  The 1D Volterra operator V on [m] has SVs sigma_k = 1/(2 sin((2k-1)pi/(4m+2))).
  The d-fold compound C_d(V) on the chamber has eigenvalues = products of d SVs.
  The reflection R flips the chamber; R-parity = (-1)^{sum of SV indices}.

  For type B, the lattice is {-m,...,m}, and the 1D Volterra has DIFFERENT structure.
  The signed lattice has size 2m+1. The SVs of the order kernel on {-m,...,m} will
  differ from the simple [m] case.

APPROACH: Rather than the Volterra SVD, directly build the comparability kernel
on the full signed lattice and restrict to the chamber.
"""

import numpy as np
from itertools import combinations, permutations, product as iprod
from scipy.linalg import eigh
from math import factorial, comb
import sys


def perm_sign(p):
    s = 0
    p = list(p)
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                s += 1
    return (-1) ** s


# ============================================================================
# TYPE A: FULL LATTICE APPROACH
# ============================================================================

def type_A_full(n, m):
    """
    Build comparability kernel on [m]^n, restrict to S_n sign-rep (= chamber kernel).
    Returns eigenvalues of the chamber kernel.
    """
    # Chamber: strictly increasing n-tuples from {0,...,m-1}
    chamber = list(combinations(range(m), n))
    N = len(chamber)
    if N == 0:
        return np.array([]), np.array([]), np.array([])

    all_perms = list(permutations(range(n)))

    # Build antisymmetrized chamber kernel
    # K_F(P,Q) = sum_{sigma in S_n} sgn(sigma) * K(P, sigma(Q))
    # where K(x,y) = 1 if x <= y componentwise OR y <= x componentwise
    K_F = np.zeros((N, N))
    for i, P in enumerate(chamber):
        for j, Q in enumerate(chamber):
            val = 0.0
            for perm in all_perms:
                Qp = tuple(Q[perm[k]] for k in range(n))
                # Check comparability
                if all(P[k] <= Qp[k] for k in range(n)) or all(Qp[k] <= P[k] for k in range(n)):
                    val += perm_sign(perm)
            K_F[i, j] = val

    evals = np.sort(np.linalg.eigvalsh(K_F))[::-1]

    # Reflection decomposition
    ch_idx = {s: i for i, s in enumerate(chamber)}
    R_mat = np.zeros((N, N))
    for i, s in enumerate(chamber):
        reflected = tuple(m - 1 - s[n - 1 - k] for k in range(n))
        if reflected in ch_idx:
            R_mat[i, ch_idx[reflected]] = 1.0

    # Check if R is an involution
    if np.allclose(R_mat @ R_mat, np.eye(N), atol=1e-10):
        P_even = 0.5 * (np.eye(N) + R_mat)
        P_odd = 0.5 * (np.eye(N) - R_mat)

        def sector_evals(P):
            ep, ev = eigh(P)
            mask = np.abs(ep - 1.0) < 1e-8
            basis = ev[:, mask]
            if basis.shape[1] == 0:
                return np.array([])
            K_sec = basis.T @ K_F @ basis
            return np.sort(np.linalg.eigvalsh(K_sec))[::-1]

        evals_even = sector_evals(P_even)
        evals_odd = sector_evals(P_odd)
    else:
        evals_even = np.array([])
        evals_odd = np.array([])

    return evals, evals_even, evals_odd


# ============================================================================
# TYPE B: SIGNED LATTICE
# ============================================================================

def type_B_full(n, m):
    """
    Build comparability kernel on {-m,...,m}^n, restrict to B_n sign-rep.

    B_n = signed permutations of {1,...,n}: permute AND optionally negate each coord.
    |B_n| = 2^n * n!

    The chamber for B_n: {0 < x_1 < x_2 < ... < x_n} in {-m,...,m}^n.
    (Strictly positive and strictly increasing.)

    K_B(P,Q) = sum_{w in B_n} det(w) * K(P, w(Q))
    where w = (sigma, epsilon), w(Q)_i = epsilon_i * Q_{sigma(i)},
    det(w) = sgn(sigma) * prod(epsilon).

    K(x,y) = 1 if x <= y or y <= x (componentwise on {-m,...,m}).
    """
    # Chamber states: strictly increasing positive tuples from {1,...,m}
    chamber = list(combinations(range(1, m + 1), n))
    N = len(chamber)
    if N == 0:
        return np.array([]), np.array([]), np.array([])

    # Generate all signed permutations
    signed_perms = []
    for perm in permutations(range(n)):
        sgn_perm = perm_sign(perm)
        for signs_tuple in iprod([-1, 1], repeat=n):
            signs = list(signs_tuple)
            det_w = sgn_perm * int(np.prod(signs))
            signed_perms.append((list(perm), signs, det_w))

    K_F = np.zeros((N, N))
    for i, P in enumerate(chamber):
        for j, Q in enumerate(chamber):
            val = 0.0
            for perm, signs, det_w in signed_perms:
                # w(Q)_k = signs[k] * Q[perm[k]]
                wQ = tuple(signs[k] * Q[perm[k]] for k in range(n))
                # Comparability in {-m,...,m}^n
                if all(P[k] <= wQ[k] for k in range(n)) or all(wQ[k] <= P[k] for k in range(n)):
                    val += det_w
            K_F[i, j] = val

    evals = np.sort(np.linalg.eigvalsh(K_F))[::-1]

    # Reflection: map x_i -> m + 1 - x_{n+1-i} (reverse and complement within {1,...,m})
    ch_idx = {s: i for i, s in enumerate(chamber)}
    R_mat = np.zeros((N, N))
    for i, s in enumerate(chamber):
        reflected = tuple(m + 1 - s[n - 1 - k] for k in range(n))
        # Check it's still in chamber
        if reflected in ch_idx:
            R_mat[i, ch_idx[reflected]] = 1.0

    if np.allclose(R_mat @ R_mat, np.eye(N), atol=1e-10):
        P_even = 0.5 * (np.eye(N) + R_mat)
        P_odd = 0.5 * (np.eye(N) - R_mat)

        def sector_evals(P):
            ep, ev = eigh(P)
            mask = np.abs(ep - 1.0) < 1e-8
            basis = ev[:, mask]
            if basis.shape[1] == 0:
                return np.array([])
            K_sec = basis.T @ K_F @ basis
            return np.sort(np.linalg.eigvalsh(K_sec))[::-1]

        evals_even = sector_evals(P_even)
        evals_odd = sector_evals(P_odd)
    else:
        evals_even = np.array([])
        evals_odd = np.array([])

    return evals, evals_even, evals_odd


# ============================================================================
# TYPE D: EVEN SIGNED PERMUTATIONS
# ============================================================================

def type_D_full(n, m):
    """
    Build comparability kernel on {-m,...,m}^n, restrict to D_n sign-rep.

    D_n = signed permutations with EVEN number of sign changes.
    |D_n| = 2^{n-1} * n!
    """
    # Chamber: same as B
    chamber = list(combinations(range(1, m + 1), n))
    N = len(chamber)
    if N == 0:
        return np.array([]), np.array([]), np.array([])

    # Generate even signed permutations
    even_signed_perms = []
    for perm in permutations(range(n)):
        sgn_perm = perm_sign(perm)
        for signs_tuple in iprod([-1, 1], repeat=n):
            signs = list(signs_tuple)
            num_neg = sum(1 for s in signs if s == -1)
            if num_neg % 2 != 0:
                continue
            det_w = sgn_perm * int(np.prod(signs))  # prod(signs) = +1 since even negs
            even_signed_perms.append((list(perm), signs, det_w))

    K_F = np.zeros((N, N))
    for i, P in enumerate(chamber):
        for j, Q in enumerate(chamber):
            val = 0.0
            for perm, signs, det_w in even_signed_perms:
                wQ = tuple(signs[k] * Q[perm[k]] for k in range(n))
                if all(P[k] <= wQ[k] for k in range(n)) or all(wQ[k] <= P[k] for k in range(n)):
                    val += det_w
            K_F[i, j] = val

    evals = np.sort(np.linalg.eigvalsh(K_F))[::-1]

    # Reflection
    ch_idx = {s: i for i, s in enumerate(chamber)}
    R_mat = np.zeros((N, N))
    for i, s in enumerate(chamber):
        reflected = tuple(m + 1 - s[n - 1 - k] for k in range(n))
        if reflected in ch_idx:
            R_mat[i, ch_idx[reflected]] = 1.0

    if np.allclose(R_mat @ R_mat, np.eye(N), atol=1e-10):
        P_even = 0.5 * (np.eye(N) + R_mat)
        P_odd = 0.5 * (np.eye(N) - R_mat)

        def sector_evals(P):
            ep, ev = eigh(P)
            mask = np.abs(ep - 1.0) < 1e-8
            basis = ev[:, mask]
            if basis.shape[1] == 0:
                return np.array([])
            K_sec = basis.T @ K_F @ basis
            return np.sort(np.linalg.eigvalsh(K_sec))[::-1]

        evals_even = sector_evals(P_even)
        evals_odd = sector_evals(P_odd)
    else:
        evals_even = np.array([])
        evals_odd = np.array([])

    return evals, evals_even, evals_odd


# ============================================================================
# COMPOUND VOLTERRA APPROACH (more direct)
# ============================================================================

def volterra_1d_order_kernel(m):
    """
    Build the lower-triangular order kernel zeta on {0,...,m-1}.
    zeta(i,j) = 1 if j <= i.
    This is a lower-triangular matrix.
    """
    Z = np.zeros((m, m))
    for i in range(m):
        for j in range(i + 1):
            Z[i, j] = 1.0
    return Z


def volterra_signed_1d(m):
    """
    Build the order kernel on {-m,...,-1,0,1,...,m} = {0,...,2m} (shifted).
    zeta(i,j) = 1 if j <= i (using natural ordering on integers).
    Size: (2m+1) x (2m+1).
    """
    N = 2 * m + 1
    Z = np.zeros((N, N))
    for i in range(N):
        for j in range(i + 1):
            Z[i, j] = 1.0
    return Z


def compound_svs(svs, d):
    """
    Compute d-fold products of singular values and their R-parity.
    For a set of SVs {sigma_1, ..., sigma_M}, the compound eigenvalues are
    sigma_{i_1} * ... * sigma_{i_d} for all i_1 < ... < i_d.
    R-parity: (-1)^{sum of 0-based indices}.
    """
    M = len(svs)
    results = []
    for indices in combinations(range(M), d):
        prod_val = 1.0
        for i in indices:
            prod_val *= svs[i]
        parity = sum(indices) % 2  # 0 = even, 1 = odd
        results.append((prod_val, indices, parity))
    results.sort(key=lambda x: -x[0])
    return results


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    np.set_printoptions(precision=8, linewidth=120)

    print("=" * 90)
    print("TYPE A, B, D ROOT SYSTEM CHAMBER KERNELS (v2 — full lattice approach)")
    print("=" * 90)

    # ==================================================================
    # SECTION 1: TYPE A REFERENCE
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 1: TYPE A REFERENCE")
    print("  Lattice: [m]^n, Group: S_n, Chamber: {x_1 < ... < x_n}")
    print("=" * 90)

    for n in [2, 3]:
        print(f"\n  --- Type A, n = {n} ---")
        print(f"  {'m':>4} {'dim':>5} {'le':>10} {'lo':>10} {'le/lo':>10}"
              f" {'le_e':>10} {'lo_o':>10} {'le_e/lo_o':>10}")

        max_m = 15 if n == 2 else 9
        for m in range(n + 1, max_m + 1):
            evals, evals_even, evals_odd = type_A_full(n, m)
            nonzero = evals[np.abs(evals) > 1e-10]
            if len(nonzero) < 2:
                continue

            le = nonzero[0]
            lo = nonzero[1]
            le_e = evals_even[0] if len(evals_even) > 0 else float('nan')
            lo_o = evals_odd[0] if len(evals_odd) > 0 else float('nan')

            ratio = le / lo
            ratio_eo = le_e / lo_o if abs(lo_o) > 1e-14 else float('inf')

            print(f"  {m:4d} {len(nonzero):5d} {le:10.4f} {lo:10.4f} {ratio:10.6f}"
                  f" {le_e:10.4f} {lo_o:10.4f} {ratio_eo:10.6f}")

        import math
        target = (n + 2) / n if n >= 2 else float('nan')
        print(f"  Expected le_e/lo_o limit: (n+2)/n = {n+2}/{n} = {target:.6f}")

    # ==================================================================
    # SECTION 2: TYPE B ON SIGNED LATTICE
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 2: TYPE B (signed lattice)")
    print("  Lattice: {-m,...,m}^n, Group: B_n (signed perms)")
    print("  Chamber: {0 < x_1 < ... < x_n <= m}")
    print("=" * 90)

    for n in [2, 3]:
        print(f"\n  --- Type B, n = {n}, |B_{n}| = {2**n * factorial(n)} ---")
        print(f"  {'m':>4} {'dim':>5} {'le':>10} {'lo':>10} {'le/lo':>10}"
              f" {'le_e':>10} {'lo_o':>10} {'le_e/lo_o':>10}")

        max_m = 12 if n == 2 else 7
        for m in range(n + 1, max_m + 1):
            evals, evals_even, evals_odd = type_B_full(n, m)
            nonzero = evals[np.abs(evals) > 1e-10]
            if len(nonzero) < 1:
                print(f"  {m:4d}   --- no nonzero eigenvalues ---")
                continue

            le = nonzero[0]
            lo = nonzero[1] if len(nonzero) >= 2 else float('nan')
            le_e = evals_even[0] if len(evals_even) > 0 else float('nan')
            lo_o = evals_odd[0] if len(evals_odd) > 0 else float('nan')

            ratio = le / lo if not np.isnan(lo) and abs(lo) > 1e-14 else float('inf')
            ratio_eo = le_e / lo_o if not np.isnan(lo_o) and abs(lo_o) > 1e-14 else float('inf')

            print(f"  {m:4d} {len(nonzero):5d} {le:10.4f} {lo:10.4f} {ratio:10.6f}"
                  f" {le_e:10.4f} {lo_o:10.4f} {ratio_eo:10.6f}")

    # ==================================================================
    # SECTION 3: TYPE D ON SIGNED LATTICE
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 3: TYPE D (signed lattice)")
    print("  Lattice: {-m,...,m}^n, Group: D_n (even signed perms)")
    print("  Chamber: {0 < x_1 < ... < x_n <= m}")
    print("=" * 90)

    for n in [2, 3, 4]:
        print(f"\n  --- Type D, n = {n}, |D_{n}| = {2**(n-1) * factorial(n)} ---")
        print(f"  {'m':>4} {'dim':>5} {'le':>10} {'lo':>10} {'le/lo':>10}"
              f" {'le_e':>10} {'lo_o':>10} {'le_e/lo_o':>10}")

        max_m = 12 if n == 2 else (7 if n == 3 else 6)
        for m in range(n + 1, max_m + 1):
            evals, evals_even, evals_odd = type_D_full(n, m)
            nonzero = evals[np.abs(evals) > 1e-10]
            if len(nonzero) < 1:
                print(f"  {m:4d}   --- no nonzero eigenvalues ---")
                continue

            le = nonzero[0]
            lo = nonzero[1] if len(nonzero) >= 2 else float('nan')
            le_e = evals_even[0] if len(evals_even) > 0 else float('nan')
            lo_o = evals_odd[0] if len(evals_odd) > 0 else float('nan')

            ratio = le / lo if not np.isnan(lo) and abs(lo) > 1e-14 else float('inf')
            ratio_eo = le_e / lo_o if not np.isnan(lo_o) and abs(lo_o) > 1e-14 else float('inf')

            print(f"  {m:4d} {len(nonzero):5d} {le:10.4f} {lo:10.4f} {ratio:10.6f}"
                  f" {le_e:10.4f} {lo_o:10.4f} {ratio_eo:10.6f}")

    # ==================================================================
    # SECTION 4: DETAILED SMALL CASES — look at the kernel matrix
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 4: DETAILED KERNEL MATRICES (small cases)")
    print("=" * 90)

    print("\n  Type A, n=2, m=4:")
    evals, ee, eo = type_A_full(2, 4)
    chamber_A = list(combinations(range(4), 2))
    print(f"  Chamber: {chamber_A}")
    print(f"  Eigenvalues: {evals}")
    print(f"  Even: {ee}")
    print(f"  Odd:  {eo}")

    print("\n  Type B, n=2, m=3:")
    evals, ee, eo = type_B_full(2, 3)
    chamber_B = list(combinations(range(1, 4), 2))
    print(f"  Chamber: {chamber_B}")
    print(f"  Eigenvalues: {evals}")
    print(f"  Even: {ee}")
    print(f"  Odd:  {eo}")

    print("\n  Type D, n=2, m=3:")
    evals, ee, eo = type_D_full(2, 3)
    chamber_D = list(combinations(range(1, 4), 2))
    print(f"  Chamber: {chamber_D}")
    print(f"  Eigenvalues: {evals}")
    print(f"  Even: {ee}")
    print(f"  Odd:  {eo}")

    # ==================================================================
    # SECTION 5: COMPOUND SVD APPROACH
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 5: COMPOUND SVD APPROACH")
    print("  1D Volterra on [m] vs 1D Volterra on [-m,...,m]")
    print("=" * 90)

    for m in [10, 20, 50]:
        # Standard Volterra on [m]
        Z_std = volterra_1d_order_kernel(m)
        _, svs_std, _ = np.linalg.svd(Z_std)
        svs_std = np.sort(svs_std)[::-1]

        # Signed Volterra on {-m,...,m}
        Z_signed = volterra_signed_1d(m)
        _, svs_signed, _ = np.linalg.svd(Z_signed)
        svs_signed = np.sort(svs_signed)[::-1]

        print(f"\n  m = {m}:")
        print(f"    Standard [m]: top SVs = {svs_std[:6]}")
        print(f"    Signed [-m,m]: top SVs = {svs_signed[:6]}")
        print(f"    Ratio signed/standard (top): {svs_signed[0]/svs_std[0]:.4f}")

    # ==================================================================
    # SECTION 6: THE KEY TEST — compound SVD on signed lattice
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 6: COMPOUND SVD ON SIGNED LATTICE")
    print("  For type B_n: use SVs from Volterra on {-m,...,m}")
    print("  Build n-fold compound, separate by parity")
    print("=" * 90)

    m = 50
    Z_signed = volterra_signed_1d(m)
    _, svs_signed, _ = np.linalg.svd(Z_signed)
    svs_signed = np.sort(svs_signed)[::-1]

    Z_std = volterra_1d_order_kernel(m)
    _, svs_std, _ = np.linalg.svd(Z_std)
    svs_std = np.sort(svs_std)[::-1]

    for n in [2, 3, 4]:
        print(f"\n  --- n = {n} ---")

        # Standard (Type A): compound of [m] SVs
        n_use = min(2 * n + 4, len(svs_std))
        comp_std = compound_svs(svs_std[:n_use], n)
        even_std = [(p, idx) for p, idx, par in comp_std if par == 0]
        odd_std = [(p, idx) for p, idx, par in comp_std if par == 1]

        if even_std and odd_std:
            ratio_A = even_std[0][0] / odd_std[0][0]
            target_A = (n + 2) / n
            print(f"    Type A (standard SVs): top_even/top_odd = {ratio_A:.6f}"
                  f"  target (n+2)/n = {target_A:.6f}")

        # Signed lattice: compound of {-m,...,m} SVs
        n_use_s = min(2 * n + 4, len(svs_signed))
        comp_signed = compound_svs(svs_signed[:n_use_s], n)
        even_signed = [(p, idx) for p, idx, par in comp_signed if par == 0]
        odd_signed = [(p, idx) for p, idx, par in comp_signed if par == 1]

        if even_signed and odd_signed:
            ratio_signed = even_signed[0][0] / odd_signed[0][0]
            print(f"    Signed lattice SVs: top_even/top_odd = {ratio_signed:.6f}")
            print(f"      Top even indices: {even_signed[0][1]}")
            print(f"      Top odd indices:  {odd_signed[0][1]}")

    # ==================================================================
    # SECTION 7: DIRECT B_n CHAMBER EIGENVALUES (printing full spectrum)
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 7: FULL SPECTRUM COMPARISON")
    print("=" * 90)

    n = 2
    for m in [4, 6, 8, 10]:
        print(f"\n  m = {m}, n = {n}:")

        eA, eeA, eoA = type_A_full(n, m)
        eB, eeB, eoB = type_B_full(n, m)
        eD, eeD, eoD = type_D_full(n, m)

        # Nonzero eigenvalues
        nzA = eA[np.abs(eA) > 1e-10]
        nzB = eB[np.abs(eB) > 1e-10]
        nzD = eD[np.abs(eD) > 1e-10]

        print(f"    Type A: {len(nzA)} nonzero evals, top 6: {nzA[:6]}")
        print(f"    Type B: {len(nzB)} nonzero evals, top 6: {nzB[:6]}")
        print(f"    Type D: {len(nzD)} nonzero evals, top 6: {nzD[:6]}")

        if len(eeA) > 0 and len(eoA) > 0:
            print(f"    Type A: le_even={eeA[0]:.6f}, lo_odd={eoA[0]:.6f}, ratio={eeA[0]/eoA[0]:.6f}")
        if len(eeB) > 0 and len(eoB) > 0:
            print(f"    Type B: le_even={eeB[0]:.6f}, lo_odd={eoB[0]:.6f}, ratio={eeB[0]/eoB[0]:.6f}")
        if len(eeD) > 0 and len(eoD) > 0:
            print(f"    Type D: le_even={eeD[0]:.6f}, lo_odd={eoD[0]:.6f}, ratio={eeD[0]/eoD[0]:.6f}")

    # ==================================================================
    # SECTION 8: CONVERGENCE TABLE
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 8: le_even/lo_odd CONVERGENCE TABLE")
    print("  Type A target: (n+2)/n")
    print("  Type B target: ???")
    print("  Type D target: ???")
    print("=" * 90)

    for n in [2, 3]:
        print(f"\n  n = {n}:")
        print(f"  {'m':>4} {'A: le_e/lo_o':>14} {'B: le_e/lo_o':>14} {'D: le_e/lo_o':>14}")
        print(f"  {'':>4} {'target ' + str((n+2)/n):>14}")

        max_m = 14 if n == 2 else 8
        for m in range(n + 1, max_m + 1):
            ratios = {}
            for label, fn in [('A', type_A_full), ('B', type_B_full), ('D', type_D_full)]:
                ev, ee, eo = fn(n, m)
                if len(ee) > 0 and len(eo) > 0 and abs(eo[0]) > 1e-14:
                    ratios[label] = ee[0] / eo[0]
                else:
                    ratios[label] = float('nan')

            print(f"  {m:4d} {ratios.get('A', float('nan')):14.8f}"
                  f" {ratios.get('B', float('nan')):14.8f}"
                  f" {ratios.get('D', float('nan')):14.8f}")

    # ==================================================================
    # SECTION 9: TYPE B le_even/lo_odd — does it converge to pi?
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 9: TYPE B RATIO CONVERGENCE — testing pi hypothesis")
    print("  pi = 3.14159265...")
    print("  3 = 3.00000000...")
    print("  sqrt(2)*pi/sqrt(3) = ???")
    print("=" * 90)

    import math

    n = 2
    print(f"\n  Type B, n = {n}: le_even/lo_odd convergence")
    print(f"  {'m':>4} {'le_e/lo_o':>14} {'delta':>14} {'ratio-pi':>14} {'ratio-3':>14}")
    prev = None
    for m in range(3, 22):
        ev, ee, eo = type_B_full(n, m)
        if len(ee) > 0 and len(eo) > 0 and abs(eo[0]) > 1e-14:
            r = ee[0] / eo[0]
            delta = r - prev if prev is not None else float('nan')
            print(f"  {m:4d} {r:14.8f} {delta:14.8f} {r - math.pi:14.8f} {r - 3:14.8f}")
            prev = r
        else:
            print(f"  {m:4d}    (no valid ratio)")
            prev = None

    # Also check n=3 B more carefully
    n = 3
    print(f"\n  Type B, n = {n}: le_even/lo_odd convergence")
    print(f"  {'m':>4} {'le_e/lo_o':>14}")
    for m in range(4, 12):
        ev, ee, eo = type_B_full(n, m)
        if len(ee) > 0 and len(eo) > 0 and abs(eo[0]) > 1e-14:
            r = ee[0] / eo[0]
            print(f"  {m:4d} {r:14.8f}")
        else:
            print(f"  {m:4d}    (no valid ratio)")

    # ==================================================================
    # SECTION 10: WHY IS TYPE B FULL KERNEL ZERO?
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 10: INVESTIGATING TYPE B KERNEL = 0")
    print("  Build the explicit kernel matrix for B_2, m=4")
    print("=" * 90)

    n = 2
    m = 4
    chamber = list(combinations(range(1, m + 1), n))
    N = len(chamber)

    # Build signed permutations
    signed_perms = []
    for perm in permutations(range(n)):
        sgn_perm = perm_sign(perm)
        for signs_tuple in iprod([-1, 1], repeat=n):
            signs = list(signs_tuple)
            det_w = sgn_perm * int(np.prod(signs))
            signed_perms.append((list(perm), signs, det_w))

    print(f"  Chamber states ({N}): {chamber}")
    print(f"  |B_2| = {len(signed_perms)}")

    # For each chamber pair (P,Q), show the group orbit contributions
    P = chamber[0]  # (1,2)
    Q = chamber[1]  # (1,3)
    print(f"\n  Detailed K_B({P}, {Q}):")
    total = 0
    for perm, signs, det_w in signed_perms:
        wQ = tuple(signs[k] * Q[perm[k]] for k in range(n))
        comp = all(P[k] <= wQ[k] for k in range(n)) or all(wQ[k] <= P[k] for k in range(n))
        if comp:
            total += det_w
            print(f"    w = perm={perm}, signs={signs}: wQ={wQ}, det={det_w:+d}, COMPARABLE")
        else:
            pass  # print(f"    w = perm={perm}, signs={signs}: wQ={wQ}, det={det_w:+d}, not comparable")
    print(f"  Total = {total}")

    # Try the order kernel (just zeta, not comparability)
    # K(x,y) = zeta(x,y) = 1 if x <= y componentwise
    print(f"\n  Now using ORDER kernel zeta(P, w(Q)) instead of comparability:")

    # Rebuild K_F with order kernel
    K_F_order = np.zeros((N, N))
    for i, P in enumerate(chamber):
        for j, Q in enumerate(chamber):
            val = 0.0
            for perm, signs, det_w in signed_perms:
                wQ = tuple(signs[k] * Q[perm[k]] for k in range(n))
                # Order: P <= wQ componentwise
                if all(P[k] <= wQ[k] for k in range(n)):
                    val += det_w
            K_F_order[i, j] = val

    print(f"  Order kernel matrix K_F^order:")
    for i in range(N):
        row = "    "
        for j in range(N):
            row += f"{K_F_order[i, j]:6.1f} "
        print(row)

    evals_order = np.sort(np.linalg.eigvalsh(K_F_order))[::-1]
    nonzero_order = evals_order[np.abs(evals_order) > 1e-10]
    print(f"  Eigenvalues: {evals_order}")
    print(f"  Nonzero eigenvalues: {nonzero_order}")

    # ==================================================================
    # SECTION 11: ALTERNATIVE B_n — use ORDER kernel not comparability
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 11: TYPE B WITH ORDER KERNEL (Volterra-style)")
    print("  K_B(P,Q) = sum_{w in B_n} det(w) * zeta(P, w(Q))")
    print("  where zeta(x,y) = 1 if x <= y componentwise")
    print("=" * 90)

    def type_B_order(n, m):
        """Type B with order kernel (zeta) instead of comparability kernel."""
        chamber = list(combinations(range(1, m + 1), n))
        N = len(chamber)
        if N == 0:
            return np.array([]), np.array([]), np.array([])

        signed_perms_local = []
        for perm in permutations(range(n)):
            sgn_perm = perm_sign(perm)
            for signs_tuple in iprod([-1, 1], repeat=n):
                signs = list(signs_tuple)
                det_w = sgn_perm * int(np.prod(signs))
                signed_perms_local.append((list(perm), signs, det_w))

        K_F = np.zeros((N, N))
        for i, P in enumerate(chamber):
            for j, Q in enumerate(chamber):
                val = 0.0
                for perm, signs, det_w in signed_perms_local:
                    wQ = tuple(signs[k] * Q[perm[k]] for k in range(n))
                    if all(P[k] <= wQ[k] for k in range(n)):
                        val += det_w
                K_F[i, j] = val

        evals = np.sort(np.linalg.eigvalsh(K_F))[::-1]

        # Reflection
        ch_idx = {s: i for i, s in enumerate(chamber)}
        R_mat = np.zeros((N, N))
        for i, s in enumerate(chamber):
            reflected = tuple(m + 1 - s[n - 1 - k] for k in range(n))
            if reflected in ch_idx:
                R_mat[i, ch_idx[reflected]] = 1.0

        if np.allclose(R_mat @ R_mat, np.eye(N), atol=1e-10):
            P_even = 0.5 * (np.eye(N) + R_mat)
            P_odd = 0.5 * (np.eye(N) - R_mat)

            def sector_evals(Proj):
                ep, ev = eigh(Proj)
                mask = np.abs(ep - 1.0) < 1e-8
                basis = ev[:, mask]
                if basis.shape[1] == 0:
                    return np.array([])
                K_sec = basis.T @ K_F @ basis
                return np.sort(np.linalg.eigvalsh(K_sec))[::-1]

            evals_even = sector_evals(P_even)
            evals_odd = sector_evals(P_odd)
        else:
            evals_even = np.array([])
            evals_odd = np.array([])

        return evals, evals_even, evals_odd

    for n in [2, 3]:
        print(f"\n  --- Type B (order kernel), n = {n} ---")
        print(f"  {'m':>4} {'dim':>5} {'le':>10} {'lo':>10} {'le/lo':>10}"
              f" {'le_e':>10} {'lo_o':>10} {'le_e/lo_o':>10}")

        max_m = 16 if n == 2 else 9
        for m in range(n + 1, max_m + 1):
            evals, evals_even, evals_odd = type_B_order(n, m)
            nonzero = evals[np.abs(evals) > 1e-10]
            if len(nonzero) < 1:
                print(f"  {m:4d}   --- no nonzero eigenvalues ---")
                continue

            le = nonzero[0]
            lo = nonzero[1] if len(nonzero) >= 2 else float('nan')
            le_e = evals_even[0] if len(evals_even) > 0 else float('nan')
            lo_o = evals_odd[0] if len(evals_odd) > 0 else float('nan')

            ratio = le / lo if not np.isnan(lo) and abs(lo) > 1e-14 else float('inf')
            ratio_eo = le_e / lo_o if not np.isnan(lo_o) and abs(lo_o) > 1e-14 else float('inf')

            print(f"  {m:4d} {len(nonzero):5d} {le:10.4f} {lo:10.4f} {ratio:10.6f}"
                  f" {le_e:10.4f} {lo_o:10.4f} {ratio_eo:10.6f}")

    # ==================================================================
    # SECTION 12: SYMMETRIZED ORDER KERNEL: K + K^T for type B
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 12: TYPE B SYMMETRIZED ORDER KERNEL (K + K^T)")
    print("=" * 90)

    def type_B_sym_order(n, m):
        """Type B with symmetrized order kernel K + K^T - I (comparability-like)."""
        chamber = list(combinations(range(1, m + 1), n))
        N = len(chamber)
        if N == 0:
            return np.array([]), np.array([]), np.array([])

        signed_perms_local = []
        for perm in permutations(range(n)):
            sgn_perm = perm_sign(perm)
            for signs_tuple in iprod([-1, 1], repeat=n):
                signs = list(signs_tuple)
                det_w = sgn_perm * int(np.prod(signs))
                signed_perms_local.append((list(perm), signs, det_w))

        # Build zeta kernel
        K_zeta = np.zeros((N, N))
        for i, P in enumerate(chamber):
            for j, Q in enumerate(chamber):
                val = 0.0
                for perm, signs, det_w in signed_perms_local:
                    wQ = tuple(signs[k] * Q[perm[k]] for k in range(n))
                    if all(P[k] <= wQ[k] for k in range(n)):
                        val += det_w
                K_zeta[i, j] = val

        # Symmetrize: K + K^T - diag (to avoid double-counting diagonal)
        K_F = K_zeta + K_zeta.T - np.diag(np.diag(K_zeta))

        evals = np.sort(np.linalg.eigvalsh(K_F))[::-1]

        ch_idx = {s: i for i, s in enumerate(chamber)}
        R_mat = np.zeros((N, N))
        for i, s in enumerate(chamber):
            reflected = tuple(m + 1 - s[n - 1 - k] for k in range(n))
            if reflected in ch_idx:
                R_mat[i, ch_idx[reflected]] = 1.0

        if np.allclose(R_mat @ R_mat, np.eye(N), atol=1e-10):
            P_even = 0.5 * (np.eye(N) + R_mat)
            P_odd = 0.5 * (np.eye(N) - R_mat)

            def sector_evals(Proj):
                ep, ev = eigh(Proj)
                mask = np.abs(ep - 1.0) < 1e-8
                basis = ev[:, mask]
                if basis.shape[1] == 0:
                    return np.array([])
                K_sec = basis.T @ K_F @ basis
                return np.sort(np.linalg.eigvalsh(K_sec))[::-1]

            evals_even = sector_evals(P_even)
            evals_odd = sector_evals(P_odd)
        else:
            evals_even = np.array([])
            evals_odd = np.array([])

        return evals, evals_even, evals_odd

    for n in [2, 3]:
        print(f"\n  --- Type B (sym order), n = {n} ---")
        print(f"  {'m':>4} {'dim':>5} {'le':>10} {'lo':>10} {'le/lo':>10}"
              f" {'le_e':>10} {'lo_o':>10} {'le_e/lo_o':>10}")

        max_m = 16 if n == 2 else 9
        for m in range(n + 1, max_m + 1):
            evals, evals_even, evals_odd = type_B_sym_order(n, m)
            nonzero = evals[np.abs(evals) > 1e-10]
            if len(nonzero) < 1:
                print(f"  {m:4d}   --- no nonzero eigenvalues ---")
                continue

            le = nonzero[0]
            lo = nonzero[1] if len(nonzero) >= 2 else float('nan')
            le_e = evals_even[0] if len(evals_even) > 0 else float('nan')
            lo_o = evals_odd[0] if len(evals_odd) > 0 else float('nan')

            ratio = le / lo if not np.isnan(lo) and abs(lo) > 1e-14 else float('inf')
            ratio_eo = le_e / lo_o if not np.isnan(lo_o) and abs(lo_o) > 1e-14 else float('inf')

            print(f"  {m:4d} {len(nonzero):5d} {le:10.4f} {lo:10.4f} {ratio:10.6f}"
                  f" {le_e:10.4f} {lo_o:10.4f} {ratio_eo:10.6f}")

    # ==================================================================
    # SECTION 13: PUSH B_2 COMPARABILITY RATIO TO LARGE m
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 13: B_2 COMPARABILITY le_even/lo_odd — large m extrapolation")
    print("  The ratio at m=21 is 3.081... and still decreasing")
    print("  Testing: does it converge to 3? to pi? to e? to something else?")
    print("=" * 90)

    n = 2
    ratios_B = []
    ms_B = []
    print(f"\n  Type B (comparability), n = {n}:")
    for m in range(3, 30):
        ev, ee, eo = type_B_full(n, m)
        if len(ee) > 0 and len(eo) > 0 and abs(eo[0]) > 1e-14:
            r = ee[0] / eo[0]
            ratios_B.append(r)
            ms_B.append(m)

    # Richardson extrapolation: assume r(m) = L + a/m + b/m^2
    # Use Aitken delta-squared for acceleration
    print(f"\n  Raw values:")
    for i in range(len(ms_B)):
        print(f"    m={ms_B[i]:3d}: ratio = {ratios_B[i]:.10f}")

    if len(ratios_B) >= 3:
        print(f"\n  Aitken delta-squared acceleration:")
        for i in range(len(ratios_B) - 2):
            s0, s1, s2 = ratios_B[i], ratios_B[i+1], ratios_B[i+2]
            denom = s2 - 2*s1 + s0
            if abs(denom) > 1e-15:
                aitken = s0 - (s1 - s0)**2 / denom
                print(f"    from m={ms_B[i]},{ms_B[i+1]},{ms_B[i+2]}: L = {aitken:.10f}")

    # Also try: assume r(m) = L + a/m
    if len(ratios_B) >= 2:
        print(f"\n  Linear extrapolation (last pairs):")
        for i in range(max(0, len(ratios_B) - 5), len(ratios_B) - 1):
            r1, r2 = ratios_B[i], ratios_B[i+1]
            m1, m2 = ms_B[i], ms_B[i+1]
            # r = L + a/m => L = (m2*r2 - m1*r1) / (m2 - m1)
            L = (m2 * r2 - m1 * r1) / (m2 - m1)
            print(f"    from m={m1},{m2}: L = {L:.10f}")

    print(f"\n  Reference values:")
    print(f"    pi     = {math.pi:.10f}")
    print(f"    e      = {math.e:.10f}")
    print(f"    3      = 3.0000000000")
    print(f"    phi^2  = {((1+math.sqrt(5))/2)**2:.10f}")

    # ==================================================================
    # SECTION 14: KEY DIAGNOSTIC — what ARE the B_2 even/odd evals?
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 14: B_2 COMPARABILITY — what are the even/odd eigenvalues?")
    print("  These are nonzero despite full spectrum being zero")
    print("  Key: the REFLECTION is not in B_2, so even/odd sectors")
    print("  are not sub-representations of the B_2 action")
    print("=" * 90)

    n = 2
    for m in [5, 8, 12]:
        ev, ee, eo = type_B_full(n, m)
        print(f"\n  m = {m}:")
        print(f"    Full eigenvalues (top 6): {ev[:6]}")
        nz_even = ee[np.abs(ee) > 1e-10]
        nz_odd = eo[np.abs(eo) > 1e-10]
        print(f"    Even sector ({len(ee)} total, {len(nz_even)} nonzero): {nz_even[:6]}")
        print(f"    Odd sector ({len(eo)} total, {len(nz_odd)} nonzero): {nz_odd[:6]}")

    # ==================================================================
    # SECTION 15: THE REAL QUESTION — does B_n have a DIFFERENT natural kernel?
    # ==================================================================
    print()
    print("=" * 90)
    print("SECTION 15: NATURAL B_n KERNEL — the Weyl character formula approach")
    print("  For type A, K_F = det(zeta(p_i, q_j))_{1<=i,j<=n}")
    print("  This is the DETERMINANTAL formula (Lindstrom-Gessel-Viennot).")
    print("  For type B, the analogous formula involves the PFAFFIAN or")
    print("  a modified determinant with reflections built in.")
    print("=" * 90)

    # The correct type B kernel uses the SCHUR-like determinant:
    # For B_n, the Weyl denominator involves:
    #   prod_{i<j} (x_i - x_j)(x_i + x_j) * prod_i x_i
    # vs type A: prod_{i<j} (x_i - x_j)
    #
    # The LGV-style kernel for B_n on the lattice:
    # K_B(P,Q) = det[zeta(p_i, q_j) - zeta(p_i, -q_j)]_{1<=i,j<=n}
    # This implements the "folded" lattice path counting.

    def type_B_determinantal(n, m):
        """
        Type B kernel via folded LGV paths.
        K_B(P,Q) = det[h(p_i, q_j)]_{1<=i,j<=n}
        where h(a, b) = zeta(a, b) - zeta(a, -b)
                      = [a <= b] - [a <= -b]
        For a >= 1, b >= 1: h(a,b) = [a <= b] - [a <= -b] = [a <= b] - 0 = [a <= b]
        Wait, that just gives the same as type A.

        Actually for B_n, the kernel should be:
        h(a, b) = zeta(a, b) - zeta(a, -b) = [a <= b] - [a <= -b]
        For a, b in {1,...,m}: a >= 1, -b <= -1, so a <= -b is always false.
        So h(a,b) = [a <= b]. Same as type A!

        The difference for B_n must come from the CHAMBER geometry.
        The B_n chamber has the EXTRA reflecting wall at x_1 = 0.
        The correct kernel uses paths on the HALF-LINE {0, 1, 2, ...} with
        a reflecting barrier at 0.

        Actually: the B_n Weyl character formula uses
        det[x_i^{lambda_j + n - j} - x_i^{-(lambda_j + n - j)}]
        vs A_n: det[x_i^{lambda_j + n - j}]

        On the lattice, this translates to:
        K_B(P,Q) = det[zeta(p_i, q_j) - zeta(-p_i, q_j)]_{i,j}
        = det[[p_i <= q_j] - [-p_i <= q_j]]_{i,j}
        = det[[p_i <= q_j] - [q_j >= -p_i]]_{i,j}

        For p_i >= 1, q_j >= 1: [q_j >= -p_i] = 1 always (since q_j >= 1 > -p_i for p_i >= 0)
        So the entry would be [p_i <= q_j] - 1.

        Hmm, that's negative for p_i > q_j. Let me think more carefully.

        The CORRECT formulation: on the 1D lattice {0, 1, ..., m}, the B-type
        1D kernel is:
        h_B(a, b) = number of lattice paths from a to b on Z_+ with reflecting wall at 0
        = zeta(a, b) + zeta(-a, b) (for the REFLECTED path)
        Wait, this is for counting, not sign.

        For the antisymmetric B-type kernel:
        h_B(a, b) = zeta(a, b) - zeta(a, -b)  (on Z, restrict to positive)
        = [a <= b] - [a <= -b]

        For a in {0,1,...,m}, b in {1,...,m}:
        If a = 0: h_B(0,b) = 1 - [0 <= -b] = 1 - 0 = 1 (since -b < 0)
        Wait, 0 <= -b iff b <= 0, which is false for b >= 1. So h_B(0,b) = 1.
        If a >= 1, b >= 1: h_B(a,b) = [a<=b] - 0 = [a<=b].

        So including 0: if we use chamber {0 <= x_1 < x_2 < ... < x_n}:
        The first coordinate can be 0. And h_B(0, q_j) = 1 for all q_j >= 1.
        This gives DIFFERENT behavior from type A where p_1 >= 1.

        Let me try: chamber = {0 <= x_1 < x_2 < ... < x_n <= m} with x_1 CAN be 0.
        Kernel: det[h_B(p_i, q_j)] where h_B(a,b) = [a<=b] if a >= 1, else 1 if a=0.
        But that's just [a<=b] since 0 <= b for all b >= 0.

        OK I think the real difference is:
        h_B(a, b) = [a <= b] - [a <= -b] on Z
        For a = 0: [0 <= b] - [0 <= -b] = 1 - [b <= 0]
          b > 0: 1 - 0 = 1
          b = 0: 1 - 1 = 0
        For a > 0, b > 0: [a<=b] - 0 = [a<=b]
        For a > 0, b = 0: [a<=0] - [a<=0] = 0

        So h_B is identical to [a<=b] on {1,...,m}, and h_B(0,b) = [b>0].
        With chamber starting at 0: this adds a row/column that's all 1s
        (well, [b>0] for b in {0,...,m} which excludes b=0).

        Actually for the proper B_n construction, the chamber should be
        {0 < x_1 < ... < x_n} or {0 <= x_1 < ... < x_n}.
        Let me try both.
        """
        # Chamber A-style: {1 <= x_1 < ... < x_n <= m}
        # with kernel h_B(a,b) = [a <= b] - [a <= -b] where a,b in {1,...,m}
        # This equals [a <= b] (since a >= 1 and -b <= -1 < 1 <= a).
        # So it's IDENTICAL to type A. Not useful.

        # Chamber with 0: {0 <= x_1 < x_2 < ... < x_n <= m}
        chamber = list(combinations(range(0, m + 1), n))
        N = len(chamber)
        if N == 0:
            return np.array([]), np.array([]), np.array([]), chamber

        def h_B(a, b):
            """B-type 1D kernel: [a <= b] - [a <= -b] on Z."""
            val = (1 if a <= b else 0) - (1 if a <= -b else 0)
            return val

        K_F = np.zeros((N, N))
        for i, P in enumerate(chamber):
            for j, Q in enumerate(chamber):
                # Determinant of [h_B(P[a], Q[b])]_{a,b=0,...,n-1}
                mat = np.array([[h_B(P[a], Q[b]) for b in range(n)] for a in range(n)])
                K_F[i, j] = np.linalg.det(mat)

        evals = np.sort(np.linalg.eigvalsh(K_F))[::-1]

        ch_idx = {s: i for i, s in enumerate(chamber)}
        R_mat = np.zeros((N, N))
        for i, s in enumerate(chamber):
            reflected = tuple(m - s[n - 1 - k] for k in range(n))
            if reflected in ch_idx:
                R_mat[i, ch_idx[reflected]] = 1.0

        evals_even = np.array([])
        evals_odd = np.array([])
        if np.allclose(R_mat @ R_mat, np.eye(N), atol=1e-10):
            P_even = 0.5 * (np.eye(N) + R_mat)
            P_odd = 0.5 * (np.eye(N) - R_mat)

            def sector_evals(Proj):
                ep, ev = eigh(Proj)
                mask = np.abs(ep - 1.0) < 1e-8
                basis = ev[:, mask]
                if basis.shape[1] == 0:
                    return np.array([])
                K_sec = basis.T @ K_F @ basis
                return np.sort(np.linalg.eigvalsh(K_sec))[::-1]

            evals_even = sector_evals(P_even)
            evals_odd = sector_evals(P_odd)

        return evals, evals_even, evals_odd, chamber

    print(f"\n  B_n DETERMINANTAL kernel (with 0 in chamber):")
    for n in [2, 3]:
        print(f"\n  --- n = {n} ---")
        print(f"  {'m':>4} {'dim':>5} {'le':>10} {'lo':>10} {'le/lo':>10}"
              f" {'le_e':>10} {'lo_o':>10} {'le_e/lo_o':>10}")

        max_m = 15 if n == 2 else 8
        for m in range(n, max_m + 1):
            evals, evals_even, evals_odd, ch = type_B_determinantal(n, m)
            nonzero = evals[np.abs(evals) > 1e-10]
            if len(nonzero) < 2:
                le_str = f"{nonzero[0]:10.4f}" if len(nonzero) > 0 else "       ---"
                print(f"  {m:4d} {len(nonzero):5d} {le_str}")
                continue

            le = nonzero[0]
            lo = nonzero[1]
            le_e = evals_even[0] if len(evals_even) > 0 else float('nan')
            lo_o = evals_odd[0] if len(evals_odd) > 0 else float('nan')

            ratio_eo = le_e / lo_o if not np.isnan(lo_o) and abs(lo_o) > 1e-14 else float('inf')

            print(f"  {m:4d} {len(nonzero):5d} {le:10.4f} {lo:10.4f} {le/lo:10.6f}"
                  f" {le_e:10.4f} {lo_o:10.4f} {ratio_eo:10.6f}")

        # Minimal case
        m_min = n
        evals, ee, eo, ch = type_B_determinantal(n, m_min)
        print(f"  Minimal m={m_min}: chamber = {ch[:6]}...")

    print()
    print("=" * 90)
    print("DONE")
    print("=" * 90)
