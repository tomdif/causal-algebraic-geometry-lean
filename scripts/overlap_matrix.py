#!/usr/bin/env python3
"""
overlap_matrix.py — The overlap matrix between compound left/right SVs

K_F = Σ_I σ_I (φ_I ψ_I^T + ψ_I φ_I^T)  where φ_I = ∧u_I, ψ_I = ∧v_I.

The eigenvalues of K_F depend on the OVERLAP MATRIX M_IJ = ⟨φ_I, ψ_J⟩.

Key facts:
  R·u_k = (-1)^k · v_k  (EXACT, from SVD analysis)
  R·φ_I = (-1)^{S(I)} · ψ_I  where S(I) = Σ_{i∈I} i

So: M_IJ = ⟨φ_I, ψ_J⟩ = (-1)^{S(J)} · ⟨φ_I, R·φ_J⟩

The eigenvalue problem for K_F reduces to a generalized matrix problem
involving M and the compound SVs σ_I.
"""

import numpy as np
from scipy.linalg import svd, eigh
from itertools import combinations
from math import comb

def zeta_matrix(m):
    T = np.zeros((m, m))
    for i in range(m):
        for j in range(i, m):
            T[i, j] = 1.0
    return T

def compound_vectors(U, d):
    """Compute compound (exterior power) vectors.
    Returns matrix whose columns are ∧_{i∈I} u_i for each d-element subset I."""
    m = U.shape[0]
    subsets = list(combinations(range(m), d))
    n_sub = len(subsets)
    # Each compound vector lives in C(m,d)-dimensional space
    chamber_states = list(combinations(range(m), d))
    n_ch = len(chamber_states)
    ch_idx = {s: i for i, s in enumerate(chamber_states)}

    Phi = np.zeros((n_ch, n_sub))
    for j, I in enumerate(subsets):
        # φ_I = ∧_{i∈I} u_i
        # In the standard chamber basis, (φ_I)_J = det U[J, I]
        for k, J in enumerate(chamber_states):
            sub = U[np.array(J), :][:, np.array(I)]
            Phi[k, j] = np.linalg.det(sub)
    return Phi, subsets

print("=" * 90)
print("THE OVERLAP MATRIX M_IJ = ⟨φ_I, ψ_J⟩")
print("=" * 90)

for d in [2, 3]:
    m = {2: 15, 3: 8}[d]
    T = zeta_matrix(m)
    U, s, Vt = svd(T)
    V = Vt.T

    # Compound vectors
    Phi, subsets = compound_vectors(U, d)  # left compound
    Psi, _ = compound_vectors(V, d)  # right compound

    n_sub = len(subsets)
    n_top = min(10, n_sub)  # look at top compound modes

    # Compound SVs (sorted by magnitude)
    comp_svs = []
    for j, I in enumerate(subsets):
        sv = np.prod([s[i] for i in I])
        comp_svs.append((sv, j, I))
    comp_svs.sort(reverse=True)

    # Reorder by compound SV magnitude
    top_indices = [c[1] for c in comp_svs[:n_top]]
    top_I = [comp_svs[k][2] for k in range(n_top)]
    top_sv = [comp_svs[k][0] for k in range(n_top)]

    # Compute overlap matrix for top modes
    M = np.zeros((n_top, n_top))
    for a in range(n_top):
        for b in range(n_top):
            ja = top_indices[a]
            jb = top_indices[b]
            M[a, b] = Phi[:, ja] @ Psi[:, jb]

    # S(I) = sum of indices in I
    S_vals = [sum(I) for I in top_I]
    parities = [(-1)**s for s in S_vals]

    print(f"\n### d={d}, m={m}")
    print(f"Top {n_top} compound modes (by SV magnitude):")
    for k in range(n_top):
        I = top_I[k]
        print(f"  #{k}: I={[i+1 for i in I]} (0-idx={list(I)}), σ_I={top_sv[k]:.4f}, "
              f"S(I)={S_vals[k]}, R-parity of (φ+ψ): {'+' if parities[k]>0 else '-'}")

    print(f"\nOverlap matrix M_IJ = ⟨φ_I, ψ_J⟩ (top {min(6,n_top)}×{min(6,n_top)}):")
    n_show = min(6, n_top)
    for a in range(n_show):
        row = " ".join(f"{M[a,b]:8.4f}" for b in range(n_show))
        print(f"  {row}")

    print(f"\nDiagonal M_II (self-overlap = cos(θ_I)):")
    for k in range(n_show):
        print(f"  I={[i+1 for i in top_I[k]]}: M_II = {M[k,k]:.6f}")

    # Build the effective Hamiltonian in the compound SVD basis
    # K_F restricted to the span of top compound vectors:
    # H_ab = σ_a · M_ab + σ_b · M_ba (approximately)
    # Actually: ⟨(φ_a+ψ_a), K_F, (φ_b+ψ_b)⟩ involves multiple terms.

    # Direct approach: project K_F onto the compound SVD basis
    # K_F = A + A^T - I where A = Σ σ_I φ_I ψ_I^T

    # Build A restricted to top modes: A_eff_ab = σ_a * ⟨φ_a, ψ_b⟩ ... no.
    # A = Σ_I σ_I φ_I ψ_I^T. So ⟨φ_a, A φ_b⟩ = Σ_I σ_I ⟨φ_a, φ_I⟩ ⟨ψ_I, φ_b⟩.
    # If φ_a = φ_{I_a} (a specific compound vector): ⟨φ_a, φ_I⟩ = δ_{a,I}.
    # So ⟨φ_a, A φ_b⟩ = σ_a · ⟨ψ_a, φ_b⟩ = σ_a · M_ba^T.

    # Similarly: ⟨ψ_a, A ψ_b⟩ = σ_b · ⟨φ_b, ψ_a⟩... hmm, getting messy.

    # Instead: project K_F onto the joint (φ, ψ) space.
    # The 2n-dimensional space spanned by φ_1,...,φ_n, ψ_1,...,ψ_n.
    # But φ and ψ are NOT orthogonal to each other.

    # Simplest: just diagonalize K_F in the R-sectors and compare.
    # We already know le/lo. The question is WHY.

    # KEY COMPUTATION: the R-sector projection of the top compound mode.

    # The compound vector φ_0 = u_0∧u_1∧...∧u_{d-1} has R-parity (-1)^{S(I₀)}.
    # φ₀+ψ₀ is in the (-1)^{S(I₀)} R-sector.
    # φ₀-ψ₀ is in the (-1)^{S(I₀)+1} R-sector.

    # The 2×2 eigenvalues for this mode: σ₀·(1+M₀₀)² and -σ₀·(1-M₀₀)² approximately.
    # But with mixing from other modes.

    # Let me compute the RAYLEIGH QUOTIENT of K_F for:
    # v_even = Σ_I c_I (φ_I + ψ_I) [R-even if parities match]
    # v_odd = Σ_I c_I (φ_I - ψ_I) [R-odd if parities match]

    # Build R in compound space
    chamber_states = list(combinations(range(m), d))
    n_ch = len(chamber_states)
    ch_idx = {s: i for i, s in enumerate(chamber_states)}
    R_ch = np.zeros((n_ch, n_ch))
    for i, s in enumerate(chamber_states):
        reflected = tuple(m-1-s[d-1-j] for j in range(d))
        R_ch[i, ch_idx[reflected]] = 1.0

    # Build K_F
    A_full = np.zeros((n_ch, n_ch))
    for j, I in enumerate(subsets):
        sv = np.prod([s[i] for i in I])
        phi = Phi[:, j]
        psi = Psi[:, j]
        A_full += sv * np.outer(phi, psi)

    K_F = A_full + A_full.T - np.eye(n_ch)

    # Verify
    Pe = (np.eye(n_ch) + R_ch) / 2
    Po = (np.eye(n_ch) - R_ch) / 2
    ee = np.sort(eigh(Pe @ K_F @ Pe, eigvals_only=True))[::-1]
    eo = np.sort(eigh(Po @ K_F @ Po, eigvals_only=True))[::-1]
    tol = 1e-8
    ee_nz = ee[np.abs(ee) > tol]
    eo_nz = eo[np.abs(eo) > tol]

    print(f"\nEigenvalue ratio: {ee_nz[0]/eo_nz[0]:.6f} (target: {(d+1)/(d-1):.6f})")

    # Now: WHICH compound modes contribute to the top even and odd eigenvectors?
    top_even_vec = eigh(Pe @ K_F @ Pe)[1][:, np.argsort(eigh(Pe @ K_F @ Pe, eigvals_only=True))[-1]]
    top_odd_vec = eigh(Po @ K_F @ Po)[1][:, np.argsort(eigh(Po @ K_F @ Po, eigvals_only=True))[-1]]

    print(f"\nProjection of top even eigenvector onto compound modes:")
    for k in range(min(5, n_top)):
        j = top_indices[k]
        # Even-projected compound vector: (φ_I + (-1)^{S(I)} ψ_I) / norm
        ep = Phi[:, j] + parities[k] * Psi[:, j]
        norm_ep = np.linalg.norm(ep)
        if norm_ep > 1e-10:
            overlap = abs(top_even_vec @ ep) / norm_ep
            print(f"  I={[i+1 for i in top_I[k]]}: |⟨ψ_e, φ+ψ⟩| = {overlap:.6f}")

    print(f"\nProjection of top odd eigenvector onto compound modes:")
    for k in range(min(5, n_top)):
        j = top_indices[k]
        op = Phi[:, j] - parities[k] * Psi[:, j]
        norm_op = np.linalg.norm(op)
        if norm_op > 1e-10:
            overlap = abs(top_odd_vec @ op) / norm_op
            print(f"  I={[i+1 for i in top_I[k]]}: |⟨ψ_o, φ-ψ⟩| = {overlap:.6f}")
