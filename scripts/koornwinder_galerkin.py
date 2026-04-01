"""
High-precision Galerkin via mpmath Gram-Schmidt orthogonalization.

Key insight: Koornwinder polynomials are NOT orthogonal with unit weight
on the simplex (they use Jacobi weight from collapsed coordinates).
There is no tensor-product orthogonal basis for flat measure on the triangle.

Solution: use monomials + Gram-Schmidt with extended precision (mpmath)
to build an orthonormal basis, then solve the Galerkin system stably.
"""
import numpy as np
from math import comb, lgamma
import time

# Try mpmath for extended precision; fall back to numpy
try:
    import mpmath
    mpmath.mp.dps = 50  # 50 decimal digits
    HAS_MPMATH = True
    print("Using mpmath with 50-digit precision")
except ImportError:
    HAS_MPMATH = False
    print("mpmath not available, using numpy float64")

def si(a, b):
    """∫_Σ u^a v^b dA = a! b! / (a+b+2)!"""
    if HAS_MPMATH:
        return float(mpmath.beta(a+1, b+1) / (a+b+2))
    return np.exp(lgamma(a+1) + lgamma(b+1) - lgamma(a+b+3))

def si_mp(a, b):
    """Extended precision simplex integral."""
    if HAS_MPMATH:
        return mpmath.beta(a+1, b+1) / (a+b+2)
    return si(a, b)

def K_mono(a, b):
    """(K u^a v^b)(u,v) as {(α,β): coeff}."""
    B = b + 1
    result = {}
    for j in range(B + 1):
        key = (a+j+1, 0)
        result[key] = result.get(key, 0.0) + ((-1)**j * comb(B,j)) / (B*(a+j+1))
    result[(a+1, B)] = result.get((a+1, B), 0.0) - 1.0 / (B*(a+1))
    return result

def build_system_extended(P):
    """Build Galerkin system with extended-precision Gram-Schmidt."""
    # Full basis (no BC constraint — for symmetrized operator)
    basis = [(a, total-a) for total in range(0, P+1) for a in range(total+1)]
    n = len(basis)

    if HAS_MPMATH:
        # Build mass matrix in mpmath
        B_mp = mpmath.matrix(n, n)
        for i in range(n):
            for j in range(i, n):
                val = si_mp(basis[i][0]+basis[j][0], basis[i][1]+basis[j][1])
                B_mp[i,j] = val
                B_mp[j,i] = val

        # Cholesky factorization in extended precision
        # B = L L^T
        L = mpmath.cholesky(B_mp)

        # Build stiffness matrix in mpmath
        A_mp = mpmath.matrix(n, n)
        for j in range(n):
            K_coeffs = K_mono(basis[j][0], basis[j][1])
            for i in range(n):
                val = mpmath.mpf(0)
                ai, bi = basis[i]
                for (alpha, beta), c in K_coeffs.items():
                    val += c * si_mp(ai + alpha, bi + beta)
                A_mp[i,j] = val

        # Symmetrize
        A_sym = mpmath.matrix(n, n)
        for i in range(n):
            for j in range(n):
                A_sym[i,j] = (A_mp[i,j] + A_mp[j,i]) / 2

        # Solve L^{-1} A_sym L^{-T} z = λ z
        L_inv = L**(-1)
        M = L_inv * A_sym * L_inv.T

        # Convert to numpy for eigendecomposition
        M_np = np.array([[float(M[i,j]) for j in range(n)] for i in range(n)])

    else:
        # Double precision fallback
        B_np = np.zeros((n,n))
        A_np = np.zeros((n,n))
        for i in range(n):
            for j in range(i, n):
                B_np[i,j] = B_np[j,i] = si(basis[i][0]+basis[j][0], basis[i][1]+basis[j][1])
        for j in range(n):
            K_coeffs = K_mono(basis[j][0], basis[j][1])
            for i in range(n):
                val = 0.0
                ai, bi = basis[i]
                for (alpha, beta), c in K_coeffs.items():
                    val += c * si(ai + alpha, bi + beta)
                A_np[i,j] = val
        A_sym_np = (A_np + A_np.T) / 2

        # SVD regularization
        from scipy.linalg import svd, eigh
        U, s, Vt = svd(B_np)
        tol = 1e-14 * s[0]
        k = np.sum(s > tol)
        S_inv_half = np.diag(1.0 / np.sqrt(s[:k]))
        V_k = Vt[:k, :].T
        M_np = S_inv_half @ (V_k.T @ A_sym_np @ V_k) @ S_inv_half

    from scipy.linalg import eigh
    evals, evecs = eigh(M_np)
    lam_s = evals[-1]
    z = evecs[:, -1]

    # Transform back to original basis
    if HAS_MPMATH:
        L_inv_T = L_inv.T
        C = np.array([float(sum(L_inv_T[i,j] * z[j] for j in range(n))) for i in range(n)])
    else:
        C = V_k @ S_inv_half @ z

    if C[0] < 0:
        C = -C

    lam_comp = 2 * lam_s

    # Compute gap from monomial representation
    # ψ = Σ C_k u^{a_k} v^{b_k}
    norm2 = sum(C[i]*C[j]*si(basis[i][0]+basis[j][0], basis[i][1]+basis[j][1])
                for i in range(n) for j in range(n))
    u_mom = sum(C[i]*C[j]*si(basis[i][0]+basis[j][0]+1, basis[i][1]+basis[j][1])
                for i in range(n) for j in range(n))
    v_mom = sum(C[i]*C[j]*si(basis[i][0]+basis[j][0], basis[i][1]+basis[j][1]+1)
                for i in range(n) for j in range(n))
    gap = 1 - (u_mom + v_mom) / norm2

    return lam_s, lam_comp, gap, n, basis

# ============================================================
print("=" * 70)
print("EXTENDED-PRECISION GALERKIN (mpmath Gram-Schmidt)")
print("=" * 70)
print()

prev_lam = 0
prev_gap = 0

for P in range(1, 18):
    t0 = time.time()
    try:
        lam_s, lam_comp, gap, n, basis = build_system_extended(P)
        t1 = time.time()
        dlam = abs(lam_comp - prev_lam) if prev_lam > 0 else 0
        dgap = abs(gap - prev_gap) if prev_gap > 0 else 0
        print(f"  P={P:2d}: n={n:4d}, λ_comp={lam_comp:.14f}, "
              f"γ={gap:.12f}, Δλ={dlam:.2e}, Δγ={dgap:.2e} [{t1-t0:.1f}s]")
        prev_lam = lam_comp
        prev_gap = gap
    except Exception as e:
        print(f"  P={P}: FAILED ({e})")
        break

print()
print(f"  Known: λ_comp ≈ 0.34916495, γ ≈ 0.27641374")
