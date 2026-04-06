#!/usr/bin/env python3
"""
compound_svd_mechanism.py — The REAL mechanism via compound SVD

KEY FACT: K_F = Λ^d(T) + Λ^d(T)^T - I
where T = 1D zeta function (upper triangular all-1s on [m]).

The SVD of T gives T = U·Σ·V^T with σ_k = 1/(2sin((2k-1)π/(4m+2))).
The compound Λ^d(T) = Λ^d(U)·Λ^d(Σ)·Λ^d(V)^T.

K_F = Λ^d(U)·D·Λ^d(V)^T + Λ^d(V)·D·Λ^d(U)^T
where D = Λ^d(Σ) = diag(σ_{i₁}·...·σ_{i_d}).

The R-reflection exchanges U and V (up to signs): R₁·U = V·S for some sign matrix.
This determines how R acts on the R-sectors of K_F.

The eigenvalue ratio comes from the INTERACTION between compound SVD modes
under the R-symmetry.
"""

import numpy as np
from scipy.linalg import eigh, svd
from itertools import combinations
from math import comb

def zeta_matrix(m):
    """1D zeta function: T(i,j) = 1 if i ≤ j."""
    T = np.zeros((m, m))
    for i in range(m):
        for j in range(i, m):
            T[i, j] = 1.0
    return T

def compound_matrix(A, d):
    """Compute the d-th compound (exterior power) matrix of A.
    Λ^d(A)[I,J] = det(A[I,J]) for d-element subsets I, J of [n]."""
    n = A.shape[0]
    subsets = list(combinations(range(n), d))
    ns = len(subsets)
    C = np.zeros((ns, ns))
    for a, I in enumerate(subsets):
        for b, J in enumerate(subsets):
            sub = A[np.ix_(list(I), list(J))]
            C[a, b] = np.linalg.det(sub)
    return C, subsets

def reflection_1d(m):
    """1D reflection: i → m-1-i."""
    R = np.zeros((m, m))
    for i in range(m):
        R[i, m-1-i] = 1.0
    return R

def reflection_compound(m, d, subsets):
    """d-th compound of the 1D reflection."""
    n = len(subsets)
    idx = {s: i for i, s in enumerate(subsets)}
    R = np.zeros((n, n))
    for i, s in enumerate(subsets):
        reflected = tuple(m - 1 - s[d-1-j] for j in range(d))
        R[i, idx[reflected]] = 1.0
    return R

print("=" * 90)
print("COMPOUND SVD MECHANISM: K_F = Λ^d(T) + Λ^d(T)^T - I")
print("=" * 90)

for d in [2, 3]:
    max_m = {2: 20, 3: 10}[d]
    print(f"\n### d={d}")
    print(f"{'m':>3} {'le/lo':>10} {'σ_d/σ_{d+1}':>12} {'compound':>10} {'target':>10}")

    for m in range(d+2, max_m+1):
        # 1. Build T and its compound
        T = zeta_matrix(m)
        A, subsets = compound_matrix(T, d)

        # 2. Build K_F = A + A^T - I (note: A has 1s on diagonal)
        ns = len(subsets)
        K_F = A + A.T - np.eye(ns)  # subtract diagonal double-counting

        # But wait: A(I,I) = det T[I,I] = 1 (T restricted to I is upper triangular with 1s)
        # And (A+A^T)(I,I) = 2. So K_F(I,I) = 2-1 = 1. ✓

        # 3. Build R and check K_F matches direct computation
        R = reflection_compound(m, d, subsets)

        # 4. Compute R-sector eigenvalues
        Pe = (np.eye(ns) + R) / 2
        Po = (np.eye(ns) - R) / 2

        Ke = Pe @ K_F @ Pe
        Ko = Po @ K_F @ Po

        ee = np.sort(eigh(Ke, eigvals_only=True))[::-1]
        eo = np.sort(eigh(Ko, eigvals_only=True))[::-1]

        tol = 1e-8
        ee_nz = ee[np.abs(ee) > tol]
        eo_nz = eo[np.abs(eo) > tol]

        if len(ee_nz) < 1 or len(eo_nz) < 1:
            continue

        le_lo = ee_nz[0] / eo_nz[0]

        # 5. SVD of T
        U_T, s_T, Vt_T = svd(T)
        # σ_k = s_T[k-1]
        if d < len(s_T):
            sv_ratio = s_T[d-1] / s_T[d]  # σ_d / σ_{d+1}
        else:
            sv_ratio = float('inf')

        # 6. Compound SVD analysis
        # The top compound SV = σ₁·...·σ_d
        # The second compound SV = σ₁·...·σ_{d-1}·σ_{d+1}
        # Ratio = σ_d/σ_{d+1}
        # But this is NOT the eigenvalue ratio of K_F = A + A^T!

        target = (d+1)/(d-1)
        print(f"{m:3d} {le_lo:10.5f} {sv_ratio:12.5f} {sv_ratio:10.5f} {target:10.5f}")

# ============================================================
# KEY TEST: Does K_F = Λ^d(T) + Λ^d(T)^T match the direct kernel?
# ============================================================
print("\n\n" + "=" * 90)
print("VERIFICATION: Does compound formula match direct computation?")
print("=" * 90)

for d, m in [(2, 8), (3, 7)]:
    T = zeta_matrix(m)
    A, subsets = compound_matrix(T, d)
    K_compound = A + A.T - np.eye(len(subsets))

    # Direct computation
    from itertools import permutations
    states = subsets
    n = len(states)
    perms = list(permutations(range(d)))
    signs = [(-1)**sum(1 for i in range(d) for j in range(i+1,d) if p[i]>p[j]) for p in perms]

    K_direct = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            val = 0
            for perm, sgn in zip(perms, signs):
                Qp = tuple(Q[perm[i]] for i in range(d))
                if all(P[i] <= Qp[i] for i in range(d)) or \
                   all(Qp[i] <= P[i] for i in range(d)):
                    val += sgn
            K_direct[a, b] = val

    K_direct_sym = (K_direct + K_direct.T) / 2

    diff = np.max(np.abs(K_compound - K_direct_sym))
    print(f"\nd={d}, m={m}: max|K_compound - K_direct_sym| = {diff:.10f}")
    if diff < 1e-8:
        print("  MATCH ✓")
    else:
        print(f"  MISMATCH! diff = {diff}")
        # Show where they differ
        for a in range(min(5, n)):
            for b in range(min(5, n)):
                if abs(K_compound[a,b] - K_direct_sym[a,b]) > 0.01:
                    print(f"    [{a},{b}]: compound={K_compound[a,b]:.4f}, direct={K_direct_sym[a,b]:.4f}")

# ============================================================
# SVD ANALYSIS: How R₁ acts on U and V
# ============================================================
print("\n\n" + "=" * 90)
print("SVD ANALYSIS: R₁ exchanges U and V")
print("=" * 90)

for m in [10, 20]:
    T = zeta_matrix(m)
    R1 = reflection_1d(m)
    U, s, Vt = svd(T)
    V = Vt.T

    # Check: R₁·T·R₁ = T^T
    RTR = R1 @ T @ R1
    diff = np.max(np.abs(RTR - T.T))
    print(f"\nm={m}: |R₁TR₁ - T^T| = {diff:.2e}")

    # R₁·U should relate to V (since R₁TR₁ = T^T = VΣU^T, so T = R₁VΣU^TR₁)
    # T = UΣV^T and T = R₁VΣ(R₁U)^T. Comparing: U = R₁V·P, V = R₁U·P for some P.
    # I.e., R₁U = V·P and R₁V = U·P.

    # Check: R₁·u_k should be proportional to v_k (or a specific v_j)
    # Compute overlap: (R₁·U)^T · V
    RU = R1 @ U
    overlap = RU.T @ V  # should be close to a permutation/sign matrix

    print(f"  |(R₁U)^T V| (should be ~permutation):")
    for k in range(min(5, m)):
        row = np.abs(overlap[k, :5])
        dominant = np.argmax(row)
        print(f"    k={k}: dominant j={dominant}, |overlap|={row[dominant]:.6f}, sign={np.sign(overlap[k,dominant]):.0f}")

    # The overlap pattern: R₁ maps u_k → ±v_k (same index, possibly with sign)
    # Check if it's ±v_k:
    for k in range(min(5, m)):
        ov = overlap[k, k]
        print(f"    u_{k}·R₁ → {ov:.6f}·v_{k} (parity: {'even' if ov > 0 else 'odd'})")
