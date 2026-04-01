"""
Derive and solve the coupled Bessel-mode eigenvalue system.

The right eigenfunction is:
  ψ_R(u,v) = Σ_{p≥1} C_p (u/v)^{p/2} J_p(2√(μuv))

The hypotenuse BC ψ_{R,u}(u, 1-u) = 0 gives:
  Σ_{p≥1} C_p (u/(1-u))^{(p-1)/2} J_{p-1}(2√(μu(1-u))) = 0  ∀ u ∈ (0,1)

Strategy: project onto a basis to get a matrix equation M(μ) · C = 0.
The eigenvalue μ is determined by det M(μ) = 0.

Basis: weighted L² on (0,1) with weight w(u) = 1.
Project the BC onto J_{q-1}(ζ(u)) · (u/(1-u))^{(q-1)/2} for q = 1,...,P.

Inner product: <f, g> = ∫₀¹ f(u) g(u) du.

Matrix: M_{qp}(μ) = ∫₀¹ (u/(1-u))^{(p-1)/2} J_{p-1}(ζ) · (u/(1-u))^{(q-1)/2} J_{q-1}(ζ) du
                   = ∫₀¹ (u/(1-u))^{(p+q-2)/2} J_{p-1}(ζ) J_{q-1}(ζ) du

where ζ(u) = 2√(μu(1-u)).

The eigenvalue condition: M(μ) has a nontrivial null vector C.
Equivalently: the smallest singular value of M(μ) vanishes at the eigenvalue.
"""
import numpy as np
from scipy.special import jv as J
from scipy.integrate import quad
from scipy.optimize import brentq
import time

def build_M(mu, P, nquad=500):
    """Build the P×P coupling matrix M(μ) by numerical quadrature."""
    # Gauss-Legendre on (0,1)
    x, w = np.polynomial.legendre.leggauss(nquad)
    u = (x + 1) / 2  # map (-1,1) to (0,1)
    wu = w / 2        # Jacobian

    # Precompute
    zeta = 2 * np.sqrt(mu * u * (1 - u))
    ratio = u / (1 - u)  # (u/(1-u))

    M = np.zeros((P, P))
    for q in range(P):
        for p in range(P):
            # M[q,p] = ∫ ratio^{(p+q)/2} J_p(ζ) J_q(ζ) du
            # where indices are shifted: mode p+1 has Bessel order p
            integrand = ratio**((p + q) / 2) * J(p, zeta) * J(q, zeta)
            M[q, p] = np.sum(integrand * wu)
    return M

def smallest_singular_value(mu, P, nquad=500):
    """Smallest singular value of M(μ) — vanishes at eigenvalue."""
    M = build_M(mu, P, nquad)
    return np.linalg.svd(M, compute_uv=False)[-1]

def find_eigenvalue(P, mu_range=(2.0, 20.0), nquad=500, nscan=200):
    """Find μ where M(μ) becomes singular."""
    mus = np.linspace(mu_range[0], mu_range[1], nscan)
    svs = [smallest_singular_value(m, P, nquad) for m in mus]
    svs = np.array(svs)

    # Find the first minimum (not just zero — numerical zeros are minima)
    # The eigenvalue is where the smallest SV reaches a minimum near zero
    min_idx = np.argmin(svs)

    if min_idx > 0 and min_idx < len(mus) - 1:
        # Refine with golden section around the minimum
        a, b = mus[max(0, min_idx-2)], mus[min(len(mus)-1, min_idx+2)]
        from scipy.optimize import minimize_scalar
        result = minimize_scalar(lambda m: smallest_singular_value(m, P, nquad),
                                bounds=(a, b), method='bounded')
        mu_opt = result.x
        sv_opt = result.fun
    else:
        mu_opt = mus[min_idx]
        sv_opt = svs[min_idx]

    return mu_opt, sv_opt, mus, svs

def extract_coefficients(mu, P, nquad=500):
    """Extract the null vector of M(μ) = the coefficients C_p."""
    M = build_M(mu, P, nquad)
    U, S, Vt = np.linalg.svd(M)
    C = Vt[-1]  # last row of Vt = right singular vector for smallest SV
    # Normalize so C_1 = 1
    C = C / C[0]
    return C

# ============================================================
print("=" * 70)
print("COUPLED BESSEL-MODE EIGENVALUE SYSTEM")
print("=" * 70)
print()
print("Eigenvalue condition: det M(μ) = 0")
print("M_{qp} = ∫₀¹ (u/(1-u))^{(p+q-2)/2} J_{p-1}(ζ) J_{q-1}(ζ) du")
print("where ζ = 2√(μu(1-u))")
print()

# Scan for eigenvalue at different truncation orders
print("Finding principal eigenvalue μ at each truncation order P:")
print("-" * 60)

results = {}
for P in range(2, 16):
    t0 = time.time()
    mu_opt, sv_min, mus, svs = find_eigenvalue(P, mu_range=(3.0, 12.0), nquad=300)
    t1 = time.time()

    # Extract coefficients
    C = extract_coefficients(mu_opt, P, nquad=300)

    # Convert to lambda and gap estimate
    lambda_s = 1.0 / mu_opt
    lambda_comp = 2.0 * lambda_s

    print(f"  P={P:2d}: μ = {mu_opt:.8f}, λ_comp = {lambda_comp:.8f}, "
          f"σ_min = {sv_min:.2e}, [{t1-t0:.2f}s]")
    if P <= 8:
        c_str = ", ".join(f"{c:.4f}" for c in C[:min(P, 6)])
        print(f"         C = [{c_str}]")

    results[P] = {'mu': mu_opt, 'lambda_comp': lambda_comp, 'sv_min': sv_min, 'C': C}

# Summary
print()
print("=" * 70)
print("CONVERGENCE")
print("=" * 70)
print(f"{'P':>4}  {'μ':>14}  {'λ_comp':>14}  {'λ_s':>14}  {'σ_min':>10}")
for P, r in results.items():
    print(f"  {P:2d}  {r['mu']:14.8f}  {r['lambda_comp']:14.8f}  "
          f"{1/r['mu']:14.8f}  {r['sv_min']:10.2e}")

# Known values
print()
print("Known: λ_comp ≈ 0.3492, μ ≈ 5.73 (from polynomial Galerkin)")
print("       γ₂ ≈ 0.27641374")
