#!/usr/bin/env python3
"""
volterra_overlap_proof.py — Compute the overlap matrix analytically

The Volterra operator V on [0,1]: Vf(x) = ∫₀ˣ f(t)dt.
Its SVD: V = Σ σ_k u_k ⊗ v_k where
  σ_k = 1/((k-½)π)  = 2/((2k-1)π)
  v_k(x) = √2 cos((k-½)πx)  [right singular: V*V v = σ² v]
  u_k(x) = √2 sin((k-½)πx)  [left singular: VV* u = σ² u]

The 1D reflection R₁: x → 1-x.
  R₁ u_k(x) = √2 sin((k-½)π(1-x)) = √2 sin((k-½)π)cos((k-½)πx) - √2 cos((k-½)π)sin((k-½)πx)

For k-½ = half-integer: sin((k-½)π) = sin((2k-1)π/2) = (-1)^{k-1} (±1 alternating).
cos((k-½)π) = cos((2k-1)π/2) = 0.

So R₁ u_k(x) = (-1)^{k-1} √2 cos((k-½)πx) = (-1)^{k-1} v_k(x).

With 0-indexing (k → k+1): R₁ u_{k+1} = (-1)^k v_{k+1}. ✓ Matches the numerical finding!

Now: the compound overlap M_IJ = ⟨φ_I, ψ_J⟩ where:
φ_I(x₁,...,x_d) = det[u_{i_a}(x_b)]_{a,b} / √(d!)  [antisymmetrized product]
ψ_J(x₁,...,x_d) = det[v_{j_a}(x_b)]_{a,b} / √(d!)

The overlap:
M_IJ = ∫_{chamber} φ_I(x) ψ_J(x) dx

where chamber = {0 < x₁ < ... < x_d < 1}.

Since φ_I and ψ_J are antisymmetric under permutations of (x₁,...,x_d):
∫_{chamber} φ_I ψ_J dx = (1/d!) ∫_{[0,1]^d} φ_I ψ_J dx

And ∫_{[0,1]^d} det[u_{i_a}(x_b)] · det[v_{j_a}(x_b)] dx₁...dx_d
= d! · det[∫₀¹ u_{i_a}(x) v_{j_b}(x) dx]_{a,b}

(by the Cauchy-Binet / Andreief identity).

So: M_IJ = det[∫₀¹ u_{i_a}(x) v_{j_b}(x) dx]_{a,b} = det[C_{i_a, j_b}]

where C_ij = ∫₀¹ u_i(x) v_j(x) dx = ∫₀¹ 2 sin((i-½)πx) cos((j-½)πx) dx.

THIS IS THE KEY: the overlap matrix M_IJ is the DETERMINANT of the
d×d submatrix of C, where C_ij = ∫₀¹ 2sin(αx)cos(βx)dx with
α = (i-½)π, β = (j-½)π.

The integral: 2∫₀¹ sin(αx)cos(βx)dx = ∫₀¹ [sin((α+β)x) + sin((α-β)x)] dx

For α ≠ β: = [-cos((α+β)x)/(α+β) - cos((α-β)x)/(α-β)]₀¹
= (1-cos(α+β))/(α+β) + (1-cos(α-β))/(α-β)

For α+β = (i+j-1)π: cos((i+j-1)π) = (-1)^{i+j-1} = -(-1)^{i+j}.
So 1-cos(α+β) = 1+(-1)^{i+j}.
= 2 if i+j even, 0 if i+j odd.

For α-β = (i-j)π: cos((i-j)π) = (-1)^{i-j}.
So 1-cos(α-β) = 1-(-1)^{i-j}.
= 0 if i-j even, 2 if i-j odd.

And α+β = (i+j-1)π, α-β = (i-j)π.

Case 1: i+j even (same parity).
Then 1-cos(α+β) = 2 and 1-cos(α-β) = 0 (since i-j has same parity as i+j).
C_ij = 2/((i+j-1)π) + 0 = 2/((i+j-1)π).

Case 2: i+j odd (different parity).
Then 1-cos(α+β) = 0 and 1-cos(α-β) = 2 (since i-j is odd).
C_ij = 0 + 2/((i-j)π) = 2/((i-j)π).  [Note: i-j ≠ 0 when i+j odd]

For i = j: α = β, so the integral is ∫₀¹ 2sin²(αx)dx = ∫₀¹ (1-cos(2αx))dx
= 1 - sin(2α)/(2α). With α = (i-½)π: 2α = (2i-1)π, sin((2i-1)π) = 0.
So C_ii = 1.

SUMMARY:
  C_ii = 1
  C_ij = 2/((i+j-1)π)  if i+j even, i≠j  [same parity indices]
  C_ij = 2/((i-j)π)     if i+j odd         [different parity indices]
"""

import numpy as np
from math import pi
from itertools import combinations

def C_matrix(n):
    """Compute the overlap matrix C_ij = ∫₀¹ u_i(x) v_j(x) dx for i,j=1..n."""
    C = np.zeros((n, n))
    for i in range(1, n+1):
        for j in range(1, n+1):
            if i == j:
                C[i-1, j-1] = 1.0
            elif (i + j) % 2 == 0:  # same parity
                C[i-1, j-1] = 2.0 / ((i + j - 1) * pi)
            else:  # different parity
                C[i-1, j-1] = 2.0 / ((i - j) * pi)
    return C

print("=" * 90)
print("THE OVERLAP MATRIX C_ij = ∫₀¹ u_i(x)v_j(x)dx")
print("=" * 90)

n = 8
C = C_matrix(n)
print(f"\nC matrix ({n}×{n}):")
for i in range(n):
    row = " ".join(f"{C[i,j]:8.4f}" for j in range(n))
    print(f"  {row}")

# Compound overlap: M_IJ = det(C[I,J])
# For d=2: M_{(i₁,i₂),(j₁,j₂)} = C_{i₁j₁}C_{i₂j₂} - C_{i₁j₂}C_{i₂j₁}

print("\n\n" + "=" * 90)
print("COMPOUND OVERLAP FOR d=2")
print("=" * 90)

d = 2
subsets = list(combinations(range(1, n+1), d))
ns = len(subsets)

# Top compound SVs (by product of 1/((2k-1)π))
comp_svs = []
for I in subsets:
    sv = np.prod([2.0/((2*k-1)*pi) for k in I])
    S_I = sum(k-1 for k in I)  # 0-indexed sum
    comp_svs.append((sv, I, S_I))
comp_svs.sort(reverse=True)

# Compute M_IJ for top compound modes
n_top = min(10, ns)
top_I = [c[1] for c in comp_svs[:n_top]]
top_sv = [c[0] for c in comp_svs[:n_top]]
top_S = [c[2] for c in comp_svs[:n_top]]

M = np.zeros((n_top, n_top))
for a in range(n_top):
    for b in range(n_top):
        I = top_I[a]
        J = top_I[b]
        sub = C[np.array([i-1 for i in I]), :][:, np.array([j-1 for j in J])]
        M[a, b] = np.linalg.det(sub)

print(f"\nTop {n_top} compound modes:")
for k in range(n_top):
    par = '+' if (-1)**top_S[k] > 0 else '-'
    print(f"  #{k}: I={top_I[k]}, σ={top_sv[k]:.6f}, S={top_S[k]}, R-par={par}")

print(f"\nCompound overlap M_IJ ({n_top}×{n_top}):")
for a in range(min(8, n_top)):
    row = " ".join(f"{M[a,b]:8.4f}" for b in range(min(8, n_top)))
    print(f"  {row}")

# Now build K_F_eff = Σ_I σ_I (M_IJ terms) in the R-sectors
# For each compound mode I, eigenvalue contribution is σ_I(1 + M_II) in the (-1)^{S(I)} sector.
# But with mixing: need to build the effective K matrix.

# The eigenvalue problem for K_F in the compound SVD basis:
# K_F ≈ Σ_{I,J} σ_I M_IJ σ_J ... no, that's not right.

# Actually: K_F = A + A^T where A = Σ_I σ_I φ_I ψ_I^T.
# ⟨φ_I + ψ_I, K_F, φ_J + ψ_J⟩ = σ_I(M_IJ + M_JI) + σ_J(M_JI + M_IJ) + ...
# This is getting complicated. Let me use a cleaner formulation.

# In the "symmetrized compound" basis: e_I^+ = (φ_I + ε_I ψ_I)/√(2(1+ε_I M_II))
# where ε_I = (-1)^{S(I)} is the R-parity sign.
# These are R-even with R e_I^+ = ε_I e_I^+... wait:
# R(φ_I + ε_I ψ_I) = ε_I ψ_I + ε_I · ε_I φ_I = ε_I(ψ_I + φ_I) = ε_I(φ_I + ψ_I)
# Hmm, that's only true if ε_I² = 1, which it is. But then:
# R(φ_I + ε_I ψ_I) = ε_I ψ_I + φ_I (since R φ_I = ε_I ψ_I and R ψ_I = ε_I φ_I).
# For ε_I = +1: R(φ+ψ) = ψ+φ = φ+ψ. R-even. ✓
# For ε_I = -1: R(φ-ψ) = -ψ+φ = φ-ψ... wait: R(φ_I - ψ_I) = ε_I ψ_I - ε_I φ_I
# = -ε_I(φ_I - ψ_I). For ε_I = -1: = (φ_I - ψ_I). R-even!

# So for EACH compound mode I:
# If ε_I = +1: φ_I + ψ_I is R-even, φ_I - ψ_I is R-odd.
# If ε_I = -1: φ_I - ψ_I is R-even, φ_I + ψ_I is R-odd.

# R-even vector from mode I: φ_I + ε_I ψ_I (with eigenvalue σ_I(1 + M_II) contribution)
# R-odd vector from mode I: φ_I - ε_I ψ_I (with eigenvalue -σ_I(1 - M_II) contribution)

# Wait, I need to be more careful. K_F(φ_I + ε_I ψ_I) involves ALL modes.

# The matrix element: ⟨φ_I + ε_I ψ_I, K_F, φ_J + ε_J ψ_J⟩
# where both are R-even (so ε_I and ε_J are chosen for even parity).

# K_F = Σ_K σ_K (φ_K ψ_K^T + ψ_K φ_K^T)

# ⟨φ_I + ε_I ψ_I, K_F, φ_J + ε_J ψ_J⟩
# = Σ_K σ_K [⟨φ_I, φ_K⟩⟨ψ_K, φ_J⟩ + ⟨φ_I, φ_K⟩⟨ψ_K, ε_J ψ_J⟩
#            + ⟨ε_I ψ_I, φ_K⟩⟨ψ_K, φ_J⟩ + ⟨ε_I ψ_I, φ_K⟩⟨ψ_K, ε_J ψ_J⟩
#            + (φ↔ψ in K_F terms)]

# Since φ_K are orthonormal: ⟨φ_I, φ_K⟩ = δ_{IK}. Similarly ⟨ψ_I, ψ_K⟩ = δ_{IK}.
# But ⟨φ_I, ψ_K⟩ = M_{IK} and ⟨ψ_I, φ_K⟩ = M_{KI}^T.

# Wait: ⟨ψ_I, φ_K⟩ = ⟨φ_K, ψ_I⟩* = M_{KI} (real).

# So:
# = Σ_K σ_K [δ_{IK} M_{KJ} + δ_{IK} ε_J δ_{KJ} + ε_I M_{KI} M_{KJ} + ε_I M_{KI} ε_J δ_{KJ}
#            + M_{IK} δ_{KJ} + M_{IK} ε_J M_{JK}... ]

# This is getting very messy. Let me just build the effective matrix numerically.

# Build the R-even projected K matrix in the compound basis:
print("\n\n" + "=" * 90)
print("R-EVEN SECTOR: Effective matrix in compound SVD basis")
print("=" * 90)

# R-even vectors from each compound mode I:
# w_I = (φ_I + ε_I ψ_I) where ε_I = (-1)^{S(I)} (the sign that makes it R-even).
# These are NOT orthonormal (they have norm² = 2(1 + ε_I M_II) and cross-overlaps).

# The Gram matrix: G_IJ = ⟨w_I, w_J⟩ = δ_{IJ} + ε_I ε_J δ_{IJ} + ε_I M_{JI} + ε_J M_{IJ}
# = 2δ_{IJ} + ε_I M_{JI} + ε_J M_{IJ}  (using ⟨φ_I,φ_J⟩ = δ_{IJ}, ⟨ψ_I,ψ_J⟩ = δ_{IJ})

# Hmm: ⟨w_I, w_J⟩ = ⟨φ_I + ε_I ψ_I, φ_J + ε_J ψ_J⟩
# = ⟨φ_I,φ_J⟩ + ε_J⟨φ_I,ψ_J⟩ + ε_I⟨ψ_I,φ_J⟩ + ε_I ε_J⟨ψ_I,ψ_J⟩
# = δ_{IJ} + ε_J M_{IJ} + ε_I M_{JI} + ε_I ε_J δ_{IJ}
# = (1 + ε_I ε_J)δ_{IJ} + ε_J M_{IJ} + ε_I M_{JI}

# For I = J: G_{II} = 2 + 2ε_I M_{II}

# The K_F matrix element:
# H_IJ = ⟨w_I, K_F w_J⟩ = Σ_K σ_K [⟨w_I, φ_K⟩⟨ψ_K, w_J⟩ + ⟨w_I, ψ_K⟩⟨φ_K, w_J⟩]
# = Σ_K σ_K [(δ_{IK} + ε_I M_{KI})(M_{KJ} + ε_J δ_{KJ}) + (M_{IK} + ε_I δ_{IK})(δ_{KJ} + ε_J M_{JK})]

# For K=I term: σ_I [(1 + ε_I M_{II})(M_{IJ} + ε_J δ_{IJ}) + (M_{II} + ε_I)(δ_{IJ} + ε_J M_{JI})]
# For K=J term: σ_J [(δ_{IJ} + ε_I M_{JI})(M_{JJ} + ε_J) + (M_{IJ} + ε_I δ_{IJ})(1 + ε_J M_{JJ})]
# For K≠I,J: σ_K [ε_I M_{KI}(M_{KJ}) + M_{IK}(ε_J M_{JK})]
#           = σ_K [ε_I M_{KI} M_{KJ} + ε_J M_{IK} M_{JK}]

# This is very complex. Let me just build it numerically for d=2.

n_eff = min(8, n_top)
eps = [(-1)**top_S[k] for k in range(n_eff)]

# Build Gram matrix G and Hamiltonian H
G = np.zeros((n_eff, n_eff))
H = np.zeros((n_eff, n_eff))

for a in range(n_eff):
    for b in range(n_eff):
        # Gram: G_ab = (1+ε_a ε_b)δ_{ab} + ε_b M_{ab} + ε_a M_{ba}
        G[a, b] = (1 + eps[a]*eps[b]) * (1 if a==b else 0) + eps[b]*M[a,b] + eps[a]*M[b,a]

        # Hamiltonian: full sum (approximate with top modes only)
        hab = 0
        for k in range(n_eff):
            # ⟨w_a, φ_K⟩ = δ_{aK} + ε_a M_{Ka}
            wphi = (1 if a==k else 0) + eps[a] * M[k, a]
            # ⟨ψ_K, w_b⟩ = M_{Kb} + ε_b δ_{Kb}
            psib = M[k, b] + eps[b] * (1 if k==b else 0)
            # ⟨w_a, ψ_K⟩ = M_{aK} + ε_a δ_{aK}
            wpsi = M[a, k] + eps[a] * (1 if a==k else 0)
            # ⟨φ_K, w_b⟩ = δ_{Kb} + ε_b M_{bK}
            phib = (1 if k==b else 0) + eps[b] * M[b, k]

            hab += top_sv[k] * (wphi * psib + wpsi * phib)
        H[a, b] = hab

# Subtract identity contribution (the -I in K_F = A + A^T - I)
H -= G  # H → H - G (since K_F = A+A^T-I, the -I contributes -⟨w_a,w_b⟩ = -G_ab)

# Solve generalized eigenvalue problem: H v = λ G v
try:
    evals = np.sort(np.linalg.eigvals(np.linalg.solve(G, H)).real)[::-1]
    print(f"\nEffective eigenvalues (d=2, even sector, top {n_eff} modes):")
    for k in range(min(5, len(evals))):
        print(f"  λ_{k+1} = {evals[k]:.6f}")
    if len(evals) >= 1:
        # Compare with actual
        from scipy.linalg import eigh as eigh2
        T_mat = np.zeros((n, n))
        for i in range(n):
            for j in range(i, n):
                T_mat[i, j] = 1.0
        # ... too complex. Just report.
        print(f"\n  Ratio info: these are EVEN-sector eigenvalues from compound SVD truncation.")
except:
    print("  Eigenvalue computation failed (singular G matrix)")

# ============================================================
# THE ANALYTICAL FORMULA
# ============================================================
print("\n\n" + "=" * 90)
print("THE ANALYTICAL C MATRIX AND ITS DETERMINANTAL STRUCTURE")
print("=" * 90)

print("""
The overlap C_ij = ∫₀¹ 2sin((i-½)πx)cos((j-½)πx)dx has the closed form:

  C_ii = 1
  C_ij = 2/((i+j-1)π)  if i≡j (mod 2), i≠j
  C_ij = 2/((i-j)π)     if i≢j (mod 2)

This means C has a BLOCK structure:
  - Diagonal blocks (same parity): C_ij = 2/((i+j-1)π)
  - Off-diagonal blocks (different parity): C_ij = 2/((i-j)π)

The compound overlap M_IJ = det(C[I,J]) is the DETERMINANT of the d×d
submatrix of C. The eigenvalue ratio (d+1)/(d-1) must emerge from the
DETERMINANTAL structure of C.

For d=2: M_{(i₁,i₂),(j₁,j₂)} = C_{i₁j₁}C_{i₂j₂} - C_{i₁j₂}C_{i₂j₁}.
""")

# Check: what is C for small indices?
print("C matrix (first 6×6):")
C6 = C_matrix(6)
for i in range(6):
    row = " ".join(f"{C6[i,j]:8.5f}" for j in range(6))
    print(f"  [{i+1}] {row}")

# The KEY: C is almost the identity (diagonal = 1) with off-diagonal entries ~ 2/(kπ).
# In the limit of large indices, off-diagonal → 0, so C → I and M → δ.
# The (d+1)/(d-1) ratio comes from the FINITE off-diagonal entries of C
# involving the first few singular vectors.

# For the TOP compound modes (involving σ₁, σ₂, σ₃):
# d=2 top: I=(1,2), J=(1,3).
# M_{(1,2),(1,3)} = C₁₁C₂₃ - C₁₃C₂₁ = 1·C₂₃ - C₁₃·C₂₁
# C₂₃: i=2,j=3, different parity. C₂₃ = 2/((2-3)π) = -2/π.
# C₁₃: i=1,j=3, same parity. C₁₃ = 2/((1+3-1)π) = 2/(3π).
# C₂₁: i=2,j=1, different parity. C₂₁ = 2/((2-1)π) = 2/π.
# M = 1·(-2/π) - (2/(3π))·(2/π) = -2/π - 4/(3π²).

M12_13 = 1*(-2/pi) - (2/(3*pi))*(2/pi)
print(f"\nM_{{(1,2),(1,3)}} = {M12_13:.6f}")
print(f"From numerical: {M[0,1]:.6f}")

# Diagonal self-overlaps:
# M_{(1,2),(1,2)} = C₁₁C₂₂ - C₁₂C₂₁
# C₁₂: different parity. = 2/((1-2)π) = -2/π.
# C₂₁: different parity. = 2/((2-1)π) = 2/π.
# M = 1·1 - (-2/π)(2/π) = 1 + 4/π².

M12_12 = 1 - (-2/pi)*(2/pi)
print(f"\nM_{{(1,2),(1,2)}} = 1 + 4/π² = {M12_12:.6f}")
print(f"From numerical: {M[0,0]:.6f}")
print(f"4/π² = {4/pi**2:.6f}")
