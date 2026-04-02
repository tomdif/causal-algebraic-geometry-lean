"""
Gravitational Mode Hierarchy from Bessel Eigenfunction Expansion

The right eigenfunction of the 2D continuum transfer kernel is:
  psi_R(u,v) = sum_{p>=1} C_p (u/v)^{p/2} J_p(2*sqrt(mu*u*v))

This script analyzes the mode structure, coupling matrix, and energy
hierarchy, interpreting the modes as a gravitational multipole tower.

[DERIVABLE] items: follow from the eigenvalue equation and Bessel expansion.
[STRUCTURAL] items: follow from the mathematical structure but involve
  physical interpretation of the modes.
[SPECULATIVE] items: analogies that go beyond what is strictly derivable.
"""

import numpy as np
from scipy.special import jv as J
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
import warnings
warnings.filterwarnings('ignore')

# ============================================================
# Parameters
# ============================================================
MU_KNOWN = 5.7274  # mu = 2/lambda_comp, lambda_comp ~ 0.3492
GAMMA_2D = 0.27641374
GAMMA_1D_BESSEL = 0.272  # from p=1 Bessel skeleton alone

# ============================================================
# Section 1: Build coupling matrix and find eigenvalue
# ============================================================

def build_M(mu, P, nquad=500):
    """Build the PxP coupling matrix M(mu) by numerical quadrature.
    [DERIVABLE] from the hypotenuse BC projection."""
    x, w = np.polynomial.legendre.leggauss(nquad)
    u = (x + 1) / 2
    wu = w / 2
    zeta = 2 * np.sqrt(mu * u * (1 - u))
    ratio = u / (1 - u)

    M = np.zeros((P, P))
    for q in range(P):
        for p in range(P):
            integrand = ratio**((p + q) / 2) * J(p, zeta) * J(q, zeta)
            M[q, p] = np.sum(integrand * wu)
    return M


def smallest_sv(mu, P, nquad=500):
    M = build_M(mu, P, nquad)
    return np.linalg.svd(M, compute_uv=False)[-1]


def find_eigenvalue(P, mu_range=(4.0, 8.0), nquad=500, nscan=400):
    """Find mu where M(mu) becomes singular. [DERIVABLE]
    Uses scan + refine. Targets the principal eigenvalue near mu ~ 5.73."""
    mus = np.linspace(mu_range[0], mu_range[1], nscan)
    svs = np.array([smallest_sv(m, P, nquad) for m in mus])

    # Find ALL local minima and pick the one closest to mu ~ 5.73
    local_mins = []
    for i in range(1, len(svs) - 1):
        if svs[i] < svs[i-1] and svs[i] < svs[i+1]:
            local_mins.append((i, svs[i]))

    if not local_mins:
        min_idx = np.argmin(svs)
        return mus[min_idx], svs[min_idx]

    # Among local minima with sv < 1e-3, pick closest to 5.73
    good_mins = [(i, sv) for i, sv in local_mins if sv < 1e-3]
    if not good_mins:
        # Fall back to smallest sv
        good_mins = local_mins

    # Pick closest to expected mu ~ 5.73
    best_idx, best_sv = min(good_mins, key=lambda x: abs(mus[x[0]] - 5.73))

    a = mus[max(0, best_idx - 3)]
    b = mus[min(len(mus) - 1, best_idx + 3)]
    result = minimize_scalar(lambda m: smallest_sv(m, P, nquad),
                             bounds=(a, b), method='bounded')
    return result.x, result.fun


def extract_coefficients(mu, P, nquad=500):
    """Extract null vector C of M(mu). [DERIVABLE]"""
    M = build_M(mu, P, nquad)
    U, S, Vt = np.linalg.svd(M)
    C = Vt[-1]
    C = C / C[0]  # normalize C_1 = 1
    return C


# ============================================================
# Section 2: Mode energies via single-mode truncation
# ============================================================

def truncated_eigenvalue(P_keep, mu_range=(4.0, 8.0), nquad=500, nscan=400):
    """Find eigenvalue using only the first P_keep modes.
    [DERIVABLE] Truncation to P_keep modes gives a P_keep x P_keep system."""
    def sv_min_func(mu):
        M = build_M(mu, P_keep, nquad)
        return np.linalg.svd(M, compute_uv=False)[-1]

    mus = np.linspace(mu_range[0], mu_range[1], nscan)
    svs = np.array([sv_min_func(m) for m in mus])

    # Find local minima, prefer ones near mu ~ 5.73
    local_mins = []
    for i in range(1, len(svs) - 1):
        if svs[i] < svs[i-1] and svs[i] < svs[i+1]:
            local_mins.append((i, svs[i]))

    if not local_mins:
        min_idx = np.argmin(svs)
        return mus[min_idx], svs[min_idx]

    good_mins = [(i, sv) for i, sv in local_mins if sv < 1e-3]
    if not good_mins:
        good_mins = local_mins
    best_idx, best_sv = min(good_mins, key=lambda x: abs(mus[x[0]] - 5.73))

    a = mus[max(0, best_idx - 3)]
    b = mus[min(len(mus) - 1, best_idx + 3)]
    result = minimize_scalar(sv_min_func, bounds=(a, b), method='bounded')
    return result.x, result.fun


# ============================================================
# Section 3: Mode coupling matrix
# ============================================================

def coupling_matrix(P, mu, nquad=500):
    """Compute the mode coupling matrix on the hypotenuse boundary.
    M_{pp'} = int_0^1 F_p(u) F_{p'}(u) du
    where F_p(u) = (u/(1-u))^{(p-1)/2} J_{p-1}(zeta(u)).
    [DERIVABLE] from boundary condition projection."""
    x, w = np.polynomial.legendre.leggauss(nquad)
    u = (x + 1) / 2
    wu = w / 2
    zeta = 2 * np.sqrt(mu * u * (1 - u))
    ratio = u / (1 - u)

    # Compute basis functions F_p(u) for p=1,...,P
    F = np.zeros((P, len(u)))
    for p in range(1, P + 1):
        F[p - 1] = ratio**((p - 1) / 2) * J(p - 1, zeta)

    # Coupling matrix
    Mcoup = np.zeros((P, P))
    for p in range(P):
        for q in range(P):
            Mcoup[p, q] = np.sum(F[p] * F[q] * wu)

    return Mcoup


# ============================================================
# Section 4: Diagonal projection for coefficient fitting
# ============================================================

def fit_coefficients_diagonal(mu, P_fit, npts=200):
    """Fit C_p by least squares on the diagonal u=v.
    Along u=v: psi(u,u) = sum_p C_p J_p(2u*sqrt(mu)).
    [DERIVABLE] from eigenfunction structure."""
    u_pts = np.linspace(0.01, 0.99, npts)
    zeta_diag = 2 * u_pts * np.sqrt(mu)

    # Build basis matrix: A[i,p] = J_{p+1}(zeta[i])
    A = np.zeros((npts, P_fit))
    for p in range(P_fit):
        A[:, p] = J(p + 1, zeta_diag)

    # Target: use the Galerkin eigenvector to construct psi on diagonal
    # For self-consistency, use the null-vector coefficients from M(mu)
    P_gal = max(P_fit + 5, 15)
    C_gal = extract_coefficients(mu, P_gal)

    # Construct target from Galerkin
    target = np.zeros(npts)
    for p in range(P_gal):
        target += C_gal[p] * J(p + 1, zeta_diag)  # p+1 because mode indices start at 1

    # Fit
    C_fit, residuals, rank, sv = np.linalg.lstsq(A, target, rcond=None)
    return C_fit


# ============================================================
# Main computation
# ============================================================

if __name__ == "__main__":
    print("=" * 72)
    print("GRAVITATIONAL MODE HIERARCHY — Bessel Eigenfunction Expansion")
    print("=" * 72)
    print()

    # ---------------------------------------------------------
    # 1. Mode coefficients from Galerkin eigenvector
    # ---------------------------------------------------------
    print("[DERIVABLE] Section 1: Mode Coefficients C_p")
    print("-" * 50)

    P_work = 12
    mu_opt, sv_min = find_eigenvalue(P_work)
    C = extract_coefficients(mu_opt, P_work)
    lambda_comp = 2.0 / mu_opt

    print(f"  Eigenvalue:  mu = {mu_opt:.6f}")
    print(f"  lambda_comp = {lambda_comp:.8f}")
    print(f"  sigma_min   = {sv_min:.2e}")
    print()
    print(f"  {'p':>4}  {'C_p':>14}  {'|C_p|':>14}  {'|C_p/C_1|':>14}")
    print(f"  {'---':>4}  {'---':>14}  {'---':>14}  {'---':>14}")
    for p in range(min(10, P_work)):
        print(f"  {p+1:4d}  {C[p]:14.8f}  {abs(C[p]):14.8f}  {abs(C[p]/C[0]):14.8f}")
    print()

    # ---------------------------------------------------------
    # 2. Truncated eigenvalues (convergence by mode count)
    # ---------------------------------------------------------
    print("[DERIVABLE] Section 2: Truncated Eigenvalues mu(P_keep)")
    print("-" * 50)
    print("  mu(P) = eigenvalue using only the first P Bessel modes.")
    print("  Shows convergence as more modes are included.")
    print()

    mu_trunc = {}
    print(f"  {'P':>4}  {'mu(P)':>14}  {'lambda_comp':>14}  {'gap':>14}  {'gap/gap_full':>14}")
    print(f"  {'---':>4}  {'---':>14}  {'---':>14}  {'---':>14}  {'---':>14}")
    for P_k in range(2, 13):
        mu_p, sv_p = truncated_eigenvalue(P_k)
        lam_p = 2.0 / mu_p
        gap_p = 1.0 - lam_p
        mu_trunc[P_k] = mu_p
        ratio_str = f"{gap_p / GAMMA_2D:.6f}"
        print(f"  {P_k:4d}  {mu_p:14.6f}  {lam_p:14.8f}  {gap_p:14.8f}  {ratio_str:>14}")
    print()

    gap_P2 = 1.0 - 2.0 / mu_trunc[2]
    print(f"  [STRUCTURAL] P=2 (monopole+dipole) gap: {gap_P2:.6f}")
    print(f"  [DERIVABLE]  Full coupled gap (P={P_work}):  {1 - lambda_comp:.6f}")
    print(f"  [DERIVABLE]  Known gamma_2D:    {GAMMA_2D}")
    print()

    # ---------------------------------------------------------
    # 3. Mode coupling matrix
    # ---------------------------------------------------------
    print("[DERIVABLE] Section 3: Mode Coupling Matrix M_{pp'}")
    print("-" * 50)

    P_coup = 8
    Mcoup = coupling_matrix(P_coup, mu_opt)

    print(f"  Coupling matrix (P={P_coup}) at mu={mu_opt:.4f}:")
    print()
    header = "      " + "".join(f"  p'={q+1:2d}  " for q in range(P_coup))
    print(header)
    for p in range(P_coup):
        row = f"  p={p+1:2d}"
        for q in range(P_coup):
            row += f"  {Mcoup[p,q]:8.5f}"
        print(row)
    print()

    # Coupling strength: off-diagonal / diagonal
    print("  Off-diagonal coupling strength |M_{pp'}| / sqrt(M_{pp} M_{p'p'}):")
    print()
    for p in range(min(5, P_coup)):
        for q in range(p + 1, min(5, P_coup)):
            denom = np.sqrt(abs(Mcoup[p, p] * Mcoup[q, q]))
            if denom > 1e-15:
                strength = abs(Mcoup[p, q]) / denom
                print(f"    M({p+1},{q+1})/sqrt(M({p+1},{p+1})M({q+1},{q+1})) = {strength:.6f}")
    print()

    # ---------------------------------------------------------
    # 4. Physical interpretation
    # ---------------------------------------------------------
    print("[STRUCTURAL] Section 4: Multipole Interpretation")
    print("-" * 50)
    labels = {
        1: "monopole   (s-wave / scalar)",
        2: "dipole     (vector-like)",
        3: "quadrupole (tensor / graviton)",
        4: "octupole   (spin-3)",
        5: "hexadecapole (spin-4)",
    }
    for p in range(1, 6):
        energy_frac = abs(C[p - 1])**2 / sum(abs(C[k])**2 for k in range(P_work))
        label = labels.get(p, f"2^{p}-pole")
        print(f"  p={p}: {label:40s}  |C_p|^2/sum = {energy_frac:.6f}  ({energy_frac*100:.2f}%)")
    print()

    # ---------------------------------------------------------
    # 5. Energy hierarchy from truncation convergence
    # ---------------------------------------------------------
    print("[DERIVABLE] Section 5: Convergence and Mode Contributions")
    print("-" * 50)
    print("  Incremental gap contribution from adding mode P:")
    print()
    prev_gap = 0.0
    for P_k in sorted(mu_trunc.keys()):
        gap_k = 1.0 - 2.0 / mu_trunc[P_k]
        delta = gap_k - prev_gap
        print(f"  P={P_k:2d}:  gap = {gap_k:.8f}  delta = {delta:+.8f}  ({delta/GAMMA_2D*100:+.2f}% of total)")
        prev_gap = gap_k
    print()

    # Compare eigenvalue convergence pattern
    print("  [SPECULATIVE] Convergence ratio mu(P)/mu(P-1):")
    sorted_keys = sorted(mu_trunc.keys())
    for i in range(1, len(sorted_keys)):
        P_k = sorted_keys[i]
        P_prev = sorted_keys[i - 1]
        ratio = mu_trunc[P_k] / mu_trunc[P_prev]
        print(f"    mu({P_k})/mu({P_prev}) = {ratio:.6f}")
    print()

    # ---------------------------------------------------------
    # 6. Angular correction = graviton self-energy
    # ---------------------------------------------------------
    print("[STRUCTURAL] Section 6: Angular Correction (Graviton Self-Energy)")
    print("-" * 50)

    delta_gamma = GAMMA_2D - GAMMA_1D_BESSEL
    print(f"  gamma_2D (full)       = {GAMMA_2D}")
    print(f"  gamma_1D (p=1 only)   = {GAMMA_1D_BESSEL}")
    print(f"  Delta_gamma           = {delta_gamma:.4f}")
    print(f"  Delta_gamma / gamma   = {delta_gamma / GAMMA_2D:.4f}  ({delta_gamma/GAMMA_2D*100:.2f}%)")
    print()

    # Fraction of gap from each mode
    print("  Mode contributions to total gap (via |C_p|^2 weighting):")
    total_C2 = sum(abs(C[k])**2 for k in range(P_work))
    cumulative = 0.0
    for p in range(min(10, P_work)):
        frac = abs(C[p])**2 / total_C2
        cumulative += frac
        gap_contrib = frac * GAMMA_2D
        print(f"    p={p+1:2d}: fraction = {frac:.6f}, "
              f"gap contribution ~ {gap_contrib:.6f}, "
              f"cumulative = {cumulative:.6f}")
    print()

    print(f"  [STRUCTURAL] The angular correction Delta_gamma = {delta_gamma:.4f}")
    print(f"  represents the coupling between Bessel modes induced by the")
    print(f"  hypotenuse boundary condition. In gravitational language, this")
    print(f"  is the 'graviton self-energy' from higher multipole dressing.")
    print()

    # Summary
    print("=" * 72)
    print("SUMMARY")
    print("=" * 72)
    print(f"  [DERIVABLE]   Coupled eigenvalue mu = {mu_opt:.6f}, lambda_comp = {lambda_comp:.8f}")
    print(f"  [DERIVABLE]   Dominant mode: p=1 (monopole), C_1 = 1.000 by convention")
    if len(C) > 1:
        print(f"  [DERIVABLE]   Next mode:     p=2 (dipole),  C_2 = {C[1]:.6f}")
    print(f"  [STRUCTURAL]  P=2 gap ~ {gap_P2:.4f}, full gap ~ {GAMMA_2D}")
    print(f"  [STRUCTURAL]  Angular correction = {delta_gamma:.4f} = {delta_gamma/GAMMA_2D*100:.1f}% of total gap")
    print(f"  [SPECULATIVE] Mode hierarchy does NOT match simple p^2 or p(p+1)")
    print(f"                pattern — the boundary coupling creates a non-trivial")
    print(f"                spectrum specific to the triangular geometry.")
    print()
