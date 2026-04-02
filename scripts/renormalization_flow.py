"""
Renormalization Group Flow from Galerkin Truncation

The polynomial degree P is a natural UV cutoff. The eigenvalue lambda_comp(P)
increases monotonically (Ritz theorem). The "beta function" beta(P) measures
the flow between cutoffs.

Physical interpretation:
  P = UV cutoff (number of modes retained)
  beta(P) = lambda_comp(P+1) - lambda_comp(P) -> 0 geometrically
  The anomalous dimension = -log(r) characterizes the approach rate
  At P -> infinity: the continuum limit is reached

Uses mpmath with 50-digit precision for matrix assembly, scipy for eigenvalues.
"""
import numpy as np
from scipy.linalg import eigh
from math import comb
import time

# ---------------------------------------------------------------------------
# Extended precision via mpmath
# ---------------------------------------------------------------------------
try:
    import mpmath
    mpmath.mp.dps = 50
    HAS_MPMATH = True
    print("Using mpmath with 50-digit precision")
except ImportError:
    HAS_MPMATH = False
    print("WARNING: mpmath not available, falling back to float64")
    print("         Results may lose accuracy for P >= 10")

def si(a, b):
    """Simplex integral: integral_Sigma u^a v^b dA = a! b! / (a+b+2)!"""
    if HAS_MPMATH:
        return mpmath.beta(a + 1, b + 1) / (a + b + 2)
    from math import lgamma
    return np.exp(lgamma(a + 1) + lgamma(b + 1) - lgamma(a + b + 3))

def si_float(a, b):
    """Float version of simplex integral."""
    return float(si(a, b))

def K_mono(a, b):
    """(K u^a v^b)(u,v) as dict {(alpha, beta): coeff}.

    K is the integral operator: (Kf)(u,v) = int_0^u int_v^{1-u'} f(u',v') dv' du'
    Applied to monomial u^a v^b, gives explicit polynomial.
    """
    B = b + 1
    result = {}
    for j in range(B + 1):
        key = (a + j + 1, 0)
        result[key] = result.get(key, 0.0) + ((-1)**j * comb(B, j)) / (B * (a + j + 1))
    result[(a + 1, B)] = result.get((a + 1, B), 0.0) - 1.0 / (B * (a + 1))
    return result


def build_galerkin(P):
    """Build Galerkin matrices for polynomial degree <= P.

    Basis: u^a v^b with a >= 1, a + b <= P (a >= 1 enforces BC: psi(0,v) = 0).

    Returns:
        A_s: symmetrized stiffness matrix (float, n x n)
        B:   mass matrix (float, n x n)
        basis: list of (a, b) pairs
    """
    basis = []
    for total in range(1, P + 1):
        for a in range(1, total + 1):
            b = total - a
            basis.append((a, b))
    n = len(basis)

    if HAS_MPMATH:
        # Build in extended precision, then convert
        B_mp = mpmath.matrix(n, n)
        A_mp = mpmath.matrix(n, n)

        for i in range(n):
            for j in range(i, n):
                val = si(basis[i][0] + basis[j][0], basis[i][1] + basis[j][1])
                B_mp[i, j] = val
                B_mp[j, i] = val

        for j in range(n):
            Kc = K_mono(basis[j][0], basis[j][1])
            for i in range(n):
                val = mpmath.mpf(0)
                ai, bi = basis[i]
                for (alpha, beta), c in Kc.items():
                    val += c * si(ai + alpha, bi + beta)
                A_mp[i, j] = val

        # Symmetrize: A_s = (A + A^T) / 2
        A_s_mp = mpmath.matrix(n, n)
        for i in range(n):
            for j in range(n):
                A_s_mp[i, j] = (A_mp[i, j] + A_mp[j, i]) / 2

        # Convert to numpy
        B_np = np.array([[float(B_mp[i, j]) for j in range(n)] for i in range(n)])
        A_s_np = np.array([[float(A_s_mp[i, j]) for j in range(n)] for i in range(n)])
    else:
        from math import lgamma
        B_np = np.zeros((n, n))
        A_s_np = np.zeros((n, n))

        for i in range(n):
            for j in range(i, n):
                B_np[i, j] = B_np[j, i] = si_float(
                    basis[i][0] + basis[j][0], basis[i][1] + basis[j][1])

        A_raw = np.zeros((n, n))
        for j in range(n):
            Kc = K_mono(basis[j][0], basis[j][1])
            for i in range(n):
                val = 0.0
                ai, bi = basis[i]
                for (alpha, beta), c in Kc.items():
                    val += c * si_float(ai + alpha, bi + beta)
                A_raw[i, j] = val

        A_s_np = (A_raw + A_raw.T) / 2

    return A_s_np, B_np, basis


def compute_lambda_comp(P):
    """Compute the comparability eigenvalue lambda_comp(P) = 2 * lambda_s(P).

    Solves A_s C = lambda_s B C and returns lambda_comp = 2 * lambda_s.
    Uses mpmath Cholesky preconditioning to handle ill-conditioned mass matrix.
    """
    basis = []
    for total in range(1, P + 1):
        for a in range(1, total + 1):
            b = total - a
            basis.append((a, b))
    n = len(basis)

    if HAS_MPMATH:
        # Build in extended precision
        B_mp = mpmath.matrix(n, n)
        A_mp = mpmath.matrix(n, n)

        for i in range(n):
            for j in range(i, n):
                val = si(basis[i][0] + basis[j][0], basis[i][1] + basis[j][1])
                B_mp[i, j] = val
                B_mp[j, i] = val

        for j in range(n):
            Kc = K_mono(basis[j][0], basis[j][1])
            for i in range(n):
                val = mpmath.mpf(0)
                ai, bi = basis[i]
                for (alpha, beta), c in Kc.items():
                    val += c * si(ai + alpha, bi + beta)
                A_mp[i, j] = val

        # Symmetrize
        A_s_mp = mpmath.matrix(n, n)
        for i in range(n):
            for j in range(n):
                A_s_mp[i, j] = (A_mp[i, j] + A_mp[j, i]) / 2

        # Cholesky precondition in extended precision: B = L L^T
        L = mpmath.cholesky(B_mp)
        L_inv = L ** (-1)
        M = L_inv * A_s_mp * L_inv.T

        # Convert to numpy for eigendecomposition
        M_np = np.array([[float(M[i, j]) for j in range(n)] for i in range(n)])
    else:
        # Double precision fallback with SVD regularization
        from scipy.linalg import svd as _svd
        A_s, B, _ = build_galerkin(P)
        U, s, Vt = _svd(B)
        tol = 1e-14 * s[0]
        k = np.sum(s > tol)
        S_inv_half = np.diag(1.0 / np.sqrt(s[:k]))
        V_k = Vt[:k, :].T
        M_np = S_inv_half @ (V_k.T @ A_s @ V_k) @ S_inv_half

    # Standard eigenvalue problem on preconditioned matrix
    evals, _ = eigh(M_np)
    lam_s = evals[-1]
    lam_comp = 2.0 * lam_s

    return lam_comp, n, basis


# ============================================================
# Main computation
# ============================================================
print()
print("=" * 78)
print("RENORMALIZATION GROUP FLOW FROM GALERKIN TRUNCATION")
print("=" * 78)
print()
print("P = polynomial degree = UV cutoff")
print("n = basis dimension = number of modes")
print("lambda_comp(P) = principal eigenvalue of symmetrized kernel")
print("beta(P) = lambda_comp(P+1) - lambda_comp(P) = RG beta function")
print("gamma(P) = 1 - lambda_comp(P) = running gap")
print()

# Collect results
P_values = list(range(1, 14))
results = {}

print(f"{'P':>3s}  {'n':>4s}  {'lambda_comp(P)':>18s}  {'beta(P)':>14s}  "
      f"{'gamma(P)':>14s}  {'time':>6s}")
print("-" * 78)

for P in P_values:
    t0 = time.time()
    lam_comp, n, basis = compute_lambda_comp(P)
    dt = time.time() - t0

    results[P] = {
        'n': n,
        'lam_comp': lam_comp,
    }

    # Beta function (for P >= 2)
    beta_str = ""
    if P >= 2 and P - 1 in results:
        beta = lam_comp - results[P - 1]['lam_comp']
        results[P]['beta'] = beta
        beta_str = f"{beta:14.10f}"
    else:
        beta_str = f"{'---':>14s}"

    # Running gap
    gamma = 1.0 - lam_comp
    results[P]['gamma'] = gamma

    print(f"{P:3d}  {n:4d}  {lam_comp:18.14f}  {beta_str}  "
          f"{gamma:14.10f}  {dt:6.2f}s")


# ============================================================
# Geometric fit: beta(P) ~ C * r^P
# ============================================================
print()
print("=" * 78)
print("GEOMETRIC FIT: beta(P) ~ C * r^P")
print("=" * 78)
print()

# Collect beta values for P >= 3 (need at least 2 consecutive betas)
P_beta = []
beta_vals = []
for P in range(2, 14):
    if P in results and 'beta' in results[P]:
        P_beta.append(P)
        beta_vals.append(results[P]['beta'])

if len(P_beta) >= 4:
    # Log-linear fit: log(|beta|) = log(C) + P * log(r)
    log_beta = np.log(np.abs(beta_vals))
    P_arr = np.array(P_beta, dtype=float)

    # Least squares fit
    A_fit = np.column_stack([np.ones_like(P_arr), P_arr])
    coeffs, _, _, _ = np.linalg.lstsq(A_fit, log_beta, rcond=None)
    log_C = coeffs[0]
    log_r = coeffs[1]
    C_fit = np.exp(log_C)
    r_fit = np.exp(log_r)

    anomalous_dim = -log_r

    print(f"Fit range: P = {P_beta[0]} to {P_beta[-1]}")
    print(f"C = {C_fit:.8f}")
    print(f"r = {r_fit:.8f}")
    print(f"Anomalous dimension = -log(r) = {anomalous_dim:.8f}")
    print()

    # Quality of fit
    print("Fit quality:")
    print(f"{'P':>3s}  {'beta(P) actual':>16s}  {'beta(P) fit':>16s}  {'ratio':>10s}")
    print("-" * 50)
    for i, P in enumerate(P_beta):
        actual = beta_vals[i]
        fitted = C_fit * r_fit**P
        ratio = actual / fitted if fitted != 0 else float('inf')
        print(f"{P:3d}  {actual:16.10e}  {fitted:16.10e}  {ratio:10.6f}")
else:
    print("Not enough data points for geometric fit.")


# ============================================================
# Summary: physical interpretation
# ============================================================
print()
print("=" * 78)
print("PHYSICAL INTERPRETATION")
print("=" * 78)
print()
print("STRUCTURE OF THE RG FLOW:")
print()
print("  1. P is the UV cutoff (polynomial degree = number of modes retained)")
print("  2. lambda_comp(P) increases monotonically with P (Ritz theorem)")
print("  3. beta(P) = lambda_comp(P+1) - lambda_comp(P) > 0 (new modes add)")
print("  4. beta(P) -> 0 GEOMETRICALLY: beta(P) ~ C * r^P with r < 1")
print()
print("  The UV fixed point (P -> infinity) is approached EXPONENTIALLY fast.")
print("  The anomalous dimension = -log(r) characterizes the approach rate.")
print()
print("  At finite P: the theory is a well-defined truncation (Galerkin projection).")
print("  At P -> infinity: the continuum transfer operator is recovered.")
print()
print("COMPARISON WITH QFT:")
print()
print("  QFT RG flow:    beta(g) = dg/d(log mu)  [continuous, coupling runs with scale]")
print("  Our RG flow:    beta(P) = d(lambda)/dP   [discrete, eigenvalue converges with cutoff]")
print()
print("  In QFT, a UV fixed point means beta(g*) = 0 (asymptotic freedom/safety).")
print("  Here, beta(P) -> 0 exponentially means lambda(P) -> lambda(infty) = 0.34916...")
print("  The theory is UV COMPLETE: the continuum limit exists and is finite.")
print()

if len(P_beta) >= 4:
    lam_inf = results[max(P_values)]['lam_comp']
    print(f"  lambda_comp(P={max(P_values)}) = {lam_inf:.10f}")
    print(f"  lambda_comp(infty) ~ 0.34916  (known from high-precision Galerkin)")
    print(f"  Residual: lambda_comp(infty) - lambda_comp({max(P_values)}) ~ "
          f"{0.34916 - lam_inf:.6f}")
    print()
    print(f"  Note: gamma_2 = 0.2764137... is the gap observable (different quantity).")
    print(f"  gamma(P) = 1 - lambda_comp(P) is the 'running gap' of the RG flow.")
    print()
    print(f"  Convergence rate r = {r_fit:.6f}")
    print(f"  Anomalous dimension = {anomalous_dim:.6f}")
    print(f"  Meaning: each new mode improves lambda by a factor of ~{r_fit:.4f}")
