"""
L² Polynomial Galerkin for the continuum transfer operator on the simplex.

Basis: φ_k(u,v) = u^{a_k} v^{b_k} with a_k ≥ 1, a_k + b_k ≤ P.
(a ≥ 1 enforces BC1: ψ(0,v) = 0.)

Galerkin system: A C = λ B C
  B_{ij} = ∫_Σ φ_i φ_j dA
  A_{ij} = ∫_Σ φ_i · (Kφ_j) dA

where (Kf)(u,v) = ∫₀ᵘ ∫_v^{1-u'} f(u',v') dv' du'

Simplex integrals: ∫_Σ u^α v^β dA = α! β! / (α+β+2)!
"""
import numpy as np
from scipy.linalg import eig
from math import lgamma, comb
import time

def simplex_integral(a, b):
    """∫_Σ u^a v^b dA = a! b! / (a+b+2)! for a,b ≥ 0."""
    return np.exp(lgamma(a+1) + lgamma(b+1) - lgamma(a+b+3))

def K_monomial_coeffs(a, b):
    """(K u^a v^b)(u,v) as dict {(α,β): coeff}.

    = (1/(b+1)) [Σ_{j=0}^{b+1} (-1)^j C(b+1,j) u^{a+j+1}/(a+j+1) - v^{b+1} u^{a+1}/(a+1)]
    """
    B = b + 1
    result = {}
    for j in range(B + 1):
        alpha, beta = a + j + 1, 0
        coeff = ((-1)**j * comb(B, j)) / (B * (a + j + 1))
        result[(alpha, beta)] = result.get((alpha, beta), 0.0) + coeff
    # Term 2
    result[(a+1, B)] = result.get((a+1, B), 0.0) - 1.0 / (B * (a+1))
    return result

def build_galerkin(P):
    """Build L² Galerkin matrices A, B for polynomial degree ≤ P."""
    basis = []
    for total in range(1, P + 1):
        for a in range(1, total + 1):
            b = total - a
            basis.append((a, b))
    n = len(basis)

    B_mat = np.zeros((n, n))
    A_mat = np.zeros((n, n))

    for i, (a_i, b_i) in enumerate(basis):
        for j, (a_j, b_j) in enumerate(basis):
            # B_{ij} = ∫ u^{a_i+a_j} v^{b_i+b_j} dA
            B_mat[i, j] = simplex_integral(a_i + a_j, b_i + b_j)

            # A_{ij} = ∫ φ_i · Kφ_j dA = Σ_{(α,β)} coeff_{αβ} ∫ u^{a_i+α} v^{b_i+β} dA
            K_coeffs = K_monomial_coeffs(a_j, b_j)
            for (alpha, beta), coeff in K_coeffs.items():
                A_mat[i, j] += coeff * simplex_integral(a_i + alpha, b_i + beta)

    return A_mat, B_mat, basis

def compute_gap_from_eigvec(c, basis):
    """Compute gap γ = 1 - <u+v>_{ψ²} from ψ = Σ c_k u^{a_k} v^{b_k}."""
    n = len(basis)
    norm2 = 0.0
    u_mom = 0.0
    v_mom = 0.0
    for i in range(n):
        for j in range(n):
            a1, b1 = basis[i]
            a2, b2 = basis[j]
            norm2 += c[i]*c[j] * simplex_integral(a1+a2, b1+b2)
            u_mom += c[i]*c[j] * simplex_integral(a1+a2+1, b1+b2)
            v_mom += c[i]*c[j] * simplex_integral(a1+a2, b1+b2+1)
    return 1 - (u_mom + v_mom) / norm2

def symmetrize_eigvec(c, basis):
    """Symmetrize: ψ_s(u,v) = ψ_R(u,v) + ψ_R(v,u).
    Coefficients: c_s[a,b] = c[a,b] + c[b,a] (if b ≥ 1)."""
    n = len(basis)
    basis_idx = {(a,b): i for i, (a,b) in enumerate(basis)}
    cs = np.copy(c)
    for i, (a, b) in enumerate(basis):
        if b >= 1 and (b, a) in basis_idx:
            cs[i] = c[i] + c[basis_idx[(b, a)]]
        # If (b,a) not in basis (b=0 means a'=0 excluded), keep as is
    return cs

# ============================================================
print("=" * 70)
print("L² POLYNOMIAL GALERKIN — CONTINUUM TRANSFER OPERATOR")
print("=" * 70)
print()
print("Galerkin: A C = λ B C")
print("A_{ij} = ∫_Σ φ_i · (Kφ_j) dA,  B_{ij} = ∫_Σ φ_i φ_j dA")
print("Basis: u^a v^b, a ≥ 1, a+b ≤ P")
print()

prev_lambda = 0
prev_gap = 0

for P in range(2, 14):
    t0 = time.time()
    A, B, basis = build_galerkin(P)
    n = len(basis)

    # Generalized eigenvalue problem A C = λ B C
    evals, evecs = eig(A, B)
    t1 = time.time()

    # Filter real eigenvalues
    real_mask = np.abs(np.imag(evals)) < 1e-10
    real_evals = np.real(evals[real_mask])
    real_evecs = np.real(evecs[:, real_mask])

    if len(real_evals) == 0:
        print(f"  P={P:2d}: no real eigenvalues!")
        continue

    # Principal eigenvalue (largest positive)
    idx_max = np.argmax(real_evals)
    lam = real_evals[idx_max]
    c = real_evecs[:, idx_max]

    # Normalize
    if c[0] < 0:
        c = -c

    # Gap from ψ_R
    gap_R = compute_gap_from_eigvec(c, basis)

    # Symmetrize and compute gap from ψ_s
    cs = symmetrize_eigvec(c, basis)
    gap_s = compute_gap_from_eigvec(cs, basis)

    # Check convergence
    dlam = abs(lam - prev_lambda) if prev_lambda > 0 else float('inf')
    dgap = abs(gap_s - prev_gap) if prev_gap > 0 else float('inf')

    # mu = 1/lambda (this lambda is for the unsymmetrized operator K)
    mu = 1.0 / lam if lam > 0 else float('inf')

    # lambda_comp = 2*lambda (comparability kernel = K + K†)
    lam_comp = 2 * lam

    print(f"  P={P:2d}: n={n:3d}, λ={lam:.11f}, λ_comp={lam_comp:.11f}, "
          f"μ={mu:.6f}, γ_R={gap_R:.10f}, γ_s={gap_s:.10f} "
          f"[Δλ={dlam:.2e}, Δγ={dgap:.2e}] {t1-t0:.2f}s")

    prev_lambda = lam
    prev_gap = gap_s

print()
print("Known: λ_comp ≈ 0.34916, γ₂ ≈ 0.27641374")
