#!/usr/bin/env python3
"""
parity_mechanism.py — Hunt for the intertwiner / ladder operator

The parity separation λ₂^even = λ₁^odd means there exists a map
T: V_odd → V_even that sends the top odd eigenvector to an even
eigenvector with the SAME eigenvalue.

Questions:
1. What is this map T concretely?
2. Does it generalize across d?
3. Does it explain why the TOP even eigenvalue is (d+1)/(d-1) times bigger?

Strategy: compute the top eigenvectors in each sector, find the
linear map between them, and look for structure.
"""

import numpy as np
from scipy.linalg import eigh
from itertools import permutations, combinations

def sign_of_perm(p):
    n = len(p)
    return (-1)**sum(1 for i in range(n) for j in range(i+1,n) if p[i] > p[j])

def chamber_kernel_and_R(m, d):
    states = list(combinations(range(m), d))
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}
    perms = list(permutations(range(d)))
    perm_signs = [sign_of_perm(p) for p in perms]

    K = np.zeros((n, n))
    for a, P in enumerate(states):
        for b, Q in enumerate(states):
            val = 0
            for perm, sgn in zip(perms, perm_signs):
                Qp = tuple(Q[perm[i]] for i in range(d))
                if all(P[i] <= Qp[i] for i in range(d)) or \
                   all(Qp[i] <= P[i] for i in range(d)):
                    val += sgn
            K[a, b] = val

    R = np.zeros((n, n))
    for i, s in enumerate(states):
        reflected = tuple(m - 1 - s[d-1-j] for j in range(d))
        R[i, idx[reflected]] = 1.0

    return K, R, states, idx

def get_sector_eigenvectors(K, R, n_top=5):
    """Get top eigenvectors in each R-sector."""
    n = K.shape[0]
    K_sym = (K + K.T) / 2
    Pe = (np.eye(n) + R) / 2
    Po = (np.eye(n) - R) / 2

    Ke = Pe @ K_sym @ Pe
    Ko = Po @ K_sym @ Po

    ee, ve = eigh(Ke)
    eo, vo = eigh(Ko)

    # Sort descending
    idx_e = np.argsort(ee)[::-1]
    idx_o = np.argsort(eo)[::-1]

    ee = ee[idx_e]
    ve = ve[:, idx_e]
    eo = eo[idx_o]
    vo = vo[:, idx_o]

    return ee, ve, eo, vo, K_sym

print("=" * 95)
print("PARITY MECHANISM: Searching for the intertwiner")
print("=" * 95)

for d in [2, 3, 4]:
    for m in [8 if d <= 3 else 7]:
        print(f"\n### d={d}, m={m}")
        K, R, states, idx = chamber_kernel_and_R(m, d)
        n = len(states)
        ee, ve, eo, vo, K_sym = get_sector_eigenvectors(K, R)

        tol = 1e-8
        ee_nz = ee[np.abs(ee) > tol]
        eo_nz = eo[np.abs(eo) > tol]

        print(f"  Top even eigenvalues: {ee_nz[:5].round(4)}")
        print(f"  Top odd eigenvalues:  {eo_nz[:5].round(4)}")
        print(f"  λ₂^even / λ₁^odd = {ee_nz[1]/eo_nz[0]:.8f}")
        print(f"  le/lo = {ee_nz[0]/eo_nz[0]:.6f}, target = {(d+1)/(d-1):.6f}")

        # The top even eigenvector
        psi_e0 = ve[:, 0]  # top even
        psi_e1 = ve[:, 1]  # second even (should match top odd eigenvalue)
        psi_o0 = vo[:, 0]  # top odd

        # Check: psi_e1 and psi_o0 have the same eigenvalue
        eval_e1 = ee[1]
        eval_o0 = eo[0]
        print(f"  λ₂^even = {eval_e1:.6f}, λ₁^odd = {eval_o0:.6f}, diff = {abs(eval_e1-eval_o0):.2e}")

        # The KEY question: what maps psi_o0 to psi_e1 (or to the even sector)?
        # Try various operators:

        # 1. Multiplication by coordinate sum Σx_i
        coord_sum = np.array([sum(s) for s in states], dtype=float)
        coord_sum_centered = coord_sum - np.mean(coord_sum)

        # S·ψ maps even → odd and odd → even (if S anti-commutes with R)
        # Check: does coord_sum commute or anti-commute with R?
        S_diag = np.diag(coord_sum_centered)
        comm = R @ S_diag - S_diag @ R
        anti = R @ S_diag + S_diag @ R
        print(f"\n  Coord sum Σx_i (centered):")
        print(f"    [R, S] norm = {np.max(np.abs(comm)):.4f}")
        print(f"    {{R, S}} norm = {np.max(np.abs(anti)):.4f}")

        # Under R: x_i → m-1-x_{d-1-i}. So Σx_i → Σ(m-1-x_i) = d(m-1) - Σx_i.
        # Centered: S_c = Σx_i - d(m-1)/2. Then R·S_c = -S_c. Anti-commutes!
        # So S_c maps even → odd and odd → even.

        # Does S_c·ψ_o0 have a large projection onto ψ_e1?
        S_psi_o = S_diag @ psi_o0
        # Project onto even sector
        S_psi_o_even = (np.eye(n) + R) / 2 @ S_psi_o
        # Overlap with ψ_e1
        overlap_e1 = abs(np.dot(S_psi_o_even, psi_e1))
        norm_S = np.linalg.norm(S_psi_o_even)
        print(f"    S·ψ_o0 projected to even: |⟨ψ_e1, P_e·S·ψ_o0⟩| / ||P_e·S·ψ_o0|| = "
              f"{overlap_e1/norm_S:.6f}" if norm_S > tol else "    zero")

        # Also check overlap with ψ_e0 (the TOP even mode)
        overlap_e0 = abs(np.dot(S_psi_o_even, psi_e0))
        print(f"    |⟨ψ_e0, P_e·S·ψ_o0⟩| / ||P_e·S·ψ_o0|| = "
              f"{overlap_e0/norm_S:.6f}" if norm_S > tol else "    zero")

        # 2. Try K itself as intertwiner: K·ψ_o0 should be λ_o0·ψ_o0 (stays in odd)
        # But K_sym·S_c maps odd → even (since K commutes with R and S anti-commutes)
        KS_psi_o = K_sym @ S_diag @ psi_o0
        KS_even = (np.eye(n) + R) / 2 @ KS_psi_o
        if np.linalg.norm(KS_even) > tol:
            ov = abs(np.dot(KS_even / np.linalg.norm(KS_even), psi_e0))
            print(f"\n  K·S·ψ_o0 projected to even:")
            print(f"    overlap with ψ_e0: {ov:.6f}")
            ov1 = abs(np.dot(KS_even / np.linalg.norm(KS_even), psi_e1))
            print(f"    overlap with ψ_e1: {ov1:.6f}")

        # 3. Try the width operator W(s) = max(s) - min(s) (for d=2, this is hi-lo)
        width = np.array([max(s) - min(s) for s in states], dtype=float)
        W_diag = np.diag(width - np.mean(width))
        comm_W = R @ W_diag - W_diag @ R
        anti_W = R @ W_diag + W_diag @ R
        print(f"\n  Width operator (centered):")
        print(f"    [R, W] norm = {np.max(np.abs(comm_W)):.4f}")
        print(f"    {{R, W}} norm = {np.max(np.abs(anti_W)):.4f}")
        # Width is R-invariant: w(R(s)) = w(s). So [R,W] = 0. Commutes!
        # W maps even → even and odd → odd. Not an intertwiner.

        # 4. The volume/area operator
        if d >= 3:
            # For d=3: "volume" = x3-x1 (range), "mid" = x2
            pass

        # 5. Try: ∂/∂c where c = center = Σx_i/d
        # This is equivalent to the coordinate sum, already tested.

        # 6. Individual coordinate differences as intertwiners
        # x_i - x_j for various i,j
        print(f"\n  Coordinate differences (centered, anti-commutation test):")
        for i_coord in range(d):
            for j_coord in range(i_coord+1, d):
                diff = np.array([s[i_coord] - s[j_coord] for s in states], dtype=float)
                diff_c = diff - np.mean(diff)
                D_diag = np.diag(diff_c)
                anti_D = R @ D_diag + D_diag @ R
                comm_D = R @ D_diag - D_diag @ R
                if np.max(np.abs(anti_D)) < 0.1:
                    D_psi_o = D_diag @ psi_o0
                    D_even = (np.eye(n) + R) / 2 @ D_psi_o
                    if np.linalg.norm(D_even) > tol:
                        ov0 = abs(np.dot(D_even/np.linalg.norm(D_even), psi_e0))
                        ov1 = abs(np.dot(D_even/np.linalg.norm(D_even), psi_e1))
                        print(f"    x_{i_coord}-x_{j_coord}: {{R,D}}={np.max(np.abs(anti_D)):.4f}, "
                              f"overlap(ψ_e0)={ov0:.4f}, overlap(ψ_e1)={ov1:.4f}")

# ============================================================
# SECTOR DIMENSION ANALYSIS
# ============================================================
print("\n\n" + "=" * 95)
print("SECTOR DIMENSIONS: n_even - n_odd pattern")
print("=" * 95)

for d in [2, 3, 4, 5]:
    print(f"\nd={d}:")
    print(f"  {'m':>3} {'n':>6} {'n_e':>6} {'n_o':>6} {'n_e-n_o':>7} {'C(⌊m/2⌋,d)':>12}")
    for m in range(d+1, min(d+12, 20)):
        n_states = int(np.math.comb(m, d))
        if n_states > 3000:
            break
        K, R, states, idx = chamber_kernel_and_R(m, d)
        n = len(states)
        # Count R-even and R-odd dimensions
        # R has eigenvalues ±1. n_even = #(+1 eigenvalues), n_odd = #(-1 eigenvalues)
        R_evals = np.linalg.eigvalsh(R)
        n_even = np.sum(R_evals > 0.5)
        n_odd = np.sum(R_evals < -0.5)
        # Guess for n_e - n_o
        h = m // 2
        guess = int(np.math.comb(h, d)) if h >= d else 0
        print(f"  {m:3d} {n:6d} {n_even:6d} {n_odd:6d} {n_even-n_odd:7d} {guess:12d}")
