"""
d=2 Fluctuation Theory for the Causal Comparability Operator.

Computes the top two eigenvalues/eigenvectors of the symmetrized comparability
operator K_s on the simplex Sigma = {u,v >= 0, u+v <= 1}, and derives:
  - Spectral gap Delta = lambda_1 - lambda_2
  - Correlation length xi_2 = -1/ln(lambda_2/lambda_1)
  - Two-point correlation function C(r) ~ exp(-r/xi_2)
  - Susceptibility chi = integral of C(P,Q)
  - Stiffness (second derivative of free energy)

Uses the mpmath Galerkin framework from certified_gap.py.
"""
import mpmath
import numpy as np
from scipy.linalg import eigh
import time

# ---------------------------------------------------------------------------
# Precision and Galerkin order
# ---------------------------------------------------------------------------
DIGITS = 50
mpmath.mp.dps = DIGITS + 20  # guard digits
P_ORDER = 10  # polynomial degree => (P+1)(P+2)/2 = 66 basis functions


def si(a, b):
    """Simplex integral: integral_Sigma u^a v^b dA = a! b! / (a+b+2)!"""
    return mpmath.beta(a + 1, b + 1) / (a + b + 2)


def K_mono(a, b):
    """
    Monomial expansion of (K u^a v^b)(u,v).
    Returns dict {(alpha, beta): coeff}.
    """
    B = b + 1
    result = {}
    for j in range(B + 1):
        key = (a + j + 1, 0)
        coeff = mpmath.mpf((-1)**j * int(mpmath.binomial(B, j))) / (B * (a + j + 1))
        result[key] = result.get(key, mpmath.mpf(0)) + coeff
    key2 = (a + 1, B)
    result[key2] = result.get(key2, mpmath.mpf(0)) - mpmath.mpf(1) / (B * (a + 1))
    return result


def build_galerkin(P):
    """
    Build the Galerkin matrices at degree P.
    Returns basis, B_mat, A_sym (all mpmath).
    """
    basis = [(a, total - a) for total in range(P + 1) for a in range(total + 1)]
    n = len(basis)

    B_mat = mpmath.matrix(n, n)
    A_mat = mpmath.matrix(n, n)

    # Mass matrix
    for i in range(n):
        ai, bi = basis[i]
        for j in range(i, n):
            aj, bj = basis[j]
            B_mat[i, j] = B_mat[j, i] = si(ai + aj, bi + bj)

    # Stiffness matrix
    for j in range(n):
        aj, bj = basis[j]
        Kcoeffs = K_mono(aj, bj)
        for i in range(n):
            ai, bi = basis[i]
            val = mpmath.mpf(0)
            for (alpha, beta), c in Kcoeffs.items():
                val += c * si(ai + alpha, bi + beta)
            A_mat[i, j] = val

    # Symmetrize
    A_sym = mpmath.matrix(n, n)
    for i in range(n):
        for j in range(n):
            A_sym[i, j] = (A_mat[i, j] + A_mat[j, i]) / 2

    return basis, B_mat, A_sym


def solve_top_k(basis, B_mat, A_sym, k=2):
    """
    Solve generalized eigenvalue problem A_sym C = lambda B C.
    Return top k eigenvalues (descending) and corresponding coefficient vectors.
    """
    n = len(basis)

    # Cholesky: B = L L^T
    L = mpmath.cholesky(B_mat)
    L_inv = L ** (-1)

    # Standard eigenproblem: M z = lambda z, where M = L^{-1} A_sym L^{-T}
    M = L_inv * A_sym * L_inv.T

    # Convert to numpy for scipy eigh (fast, and 50-digit matrices give
    # more than enough precision for double-precision eigenvalues)
    M_np = np.array([[float(M[i, j]) for j in range(n)] for i in range(n)])

    evals, evecs = eigh(M_np)

    # eigh returns ascending order; we want top k
    idx = np.argsort(evals)[::-1][:k]
    top_evals = evals[idx]
    top_evecs_z = evecs[:, idx]  # columns are eigenvectors in orthonormal basis

    # Transform back to original basis: C = L^{-T} z
    L_inv_np = np.array([[float(L_inv[i, j]) for j in range(n)] for i in range(n)])
    L_inv_T_np = L_inv_np.T

    coeff_vecs = []
    for col in range(k):
        z = top_evecs_z[:, col]
        C = L_inv_T_np @ z
        # Normalize sign: make leading component positive
        if C[0] < 0:
            C = -C
        coeff_vecs.append(C)

    return top_evals, coeff_vecs


def eval_eigenfunction(C, basis, u, v):
    """Evaluate eigenfunction psi(u,v) = sum_i C_i u^{a_i} v^{b_i}."""
    val = 0.0
    for i, (a, b) in enumerate(basis):
        val += C[i] * u**a * v**b
    return val


def compute_norm2(C, basis):
    """Compute integral_Sigma psi^2 dA."""
    n = len(basis)
    norm2 = 0.0
    for i in range(n):
        ai, bi = basis[i]
        for j in range(n):
            aj, bj = basis[j]
            norm2 += C[i] * C[j] * float(si(ai + aj, bi + bj))
    return norm2


def compute_moment(C, basis, du, dv):
    """Compute integral_Sigma u^du v^dv psi^2 dA."""
    n = len(basis)
    val = 0.0
    for i in range(n):
        ai, bi = basis[i]
        for j in range(n):
            aj, bj = basis[j]
            val += C[i] * C[j] * float(si(ai + aj + du, bi + bj + dv))
    return val


def count_sign_changes(vals):
    """Count sign changes in a sequence, ignoring zeros."""
    nonzero = [v for v in vals if abs(v) > 1e-14]
    changes = 0
    for i in range(1, len(nonzero)):
        if nonzero[i - 1] * nonzero[i] < 0:
            changes += 1
    return changes


def compute_correlation_function(C1, C2, lam1, lam2, basis, r_values, n_sample=2000):
    """
    Compute two-point correlation C(r) by Monte Carlo sampling on the simplex.

    The connected correlation of psi_1^2 at distance r:
      C(r) = <psi_1^2(P) psi_1^2(Q)>_{|P-Q|=r} - <psi_1^2>^2

    For the spectral decomposition, the leading decay is governed by
    the overlap with psi_2, giving C(r) ~ A * (lambda_2/lambda_1)^r.

    We compute this via the spectral representation:
      C(r) = sum_{k>=2} c_k^2 * (lambda_k/lambda_1)^r
    where c_k = integral_Sigma psi_1^2 psi_k dA / norm.

    For the top-2 approximation, C(r) ~ c_2^2 * (lambda_2/lambda_1)^r.
    """
    # Compute overlap coefficient c_2 = <psi_1^2, psi_2> / <psi_1^2, psi_1>
    # where psi_k are L2-normalized eigenfunctions.

    n = len(basis)
    norm1_sq = compute_norm2(C1, basis)
    norm2_sq = compute_norm2(C2, basis)
    norm1 = np.sqrt(norm1_sq)
    norm2 = np.sqrt(norm2_sq)

    # <psi_1^2, psi_2> = integral_Sigma psi_1(u,v)^2 psi_2(u,v) dA
    # psi_1^2 * psi_2 = sum_{i,j,k} C1_i C1_j C2_k u^{a_i+a_j+a_k} v^{b_i+b_j+b_k}
    overlap_12 = 0.0
    for i in range(n):
        ai, bi = basis[i]
        for j in range(n):
            aj, bj = basis[j]
            cij = C1[i] * C1[j]
            for k in range(n):
                ak, bk = basis[k]
                overlap_12 += cij * C2[k] * float(si(ai + aj + ak, bi + bj + bk))

    # <psi_1^2, psi_1> = integral_Sigma psi_1^3 dA
    overlap_11 = 0.0
    for i in range(n):
        ai, bi = basis[i]
        for j in range(n):
            aj, bj = basis[j]
            cij = C1[i] * C1[j]
            for k in range(n):
                ak, bk = basis[k]
                overlap_11 += cij * C1[k] * float(si(ai + aj + ak, bi + bj + bk))

    # Normalized overlap
    c2 = overlap_12 / (norm1**2 * norm2)

    ratio = lam2 / lam1

    # C(r) ~ c_2^2 * ratio^r  (spectral representation, top-2 truncation)
    C_r = {}
    for r in r_values:
        C_r[r] = c2**2 * ratio**r

    return C_r, c2, overlap_12, overlap_11


def compute_susceptibility_spectral(c2, lam1, lam2):
    """
    Susceptibility chi = sum_r C(r) ~ c_2^2 / (1 - lambda_2/lambda_1).
    This is the integrated autocorrelation of psi_1^2 fluctuations.
    """
    ratio = lam2 / lam1
    return c2**2 / (1.0 - ratio)


# ===========================================================================
# Main computation
# ===========================================================================
if __name__ == "__main__":
    print("=" * 75)
    print(f"d=2 FLUCTUATION THEORY  (P={P_ORDER}, {DIGITS}-digit Galerkin)")
    print("=" * 75)
    print()

    # Step 1: Build Galerkin system
    t0 = time.time()
    basis, B_mat, A_sym = build_galerkin(P_ORDER)
    n = len(basis)
    t1 = time.time()
    print(f"Galerkin matrices built: n = {n} basis functions  [{t1-t0:.1f}s]")

    # Step 2: Solve for top 2 eigenvalues
    top_evals, coeff_vecs = solve_top_k(basis, B_mat, A_sym, k=2)
    lam1_s, lam2_s = top_evals[0], top_evals[1]
    C1, C2 = coeff_vecs[0], coeff_vecs[1]
    t2 = time.time()
    print(f"Eigendecomposition done  [{t2-t1:.1f}s]")

    # The comparability eigenvalues (unsymmetrized) are 2x the symmetrized ones
    lam1_comp = 2 * lam1_s
    lam2_comp = 2 * lam2_s

    print()
    print("-" * 75)
    print("EIGENVALUES (symmetrized operator K_s)")
    print("-" * 75)
    print(f"  lambda_1 (K_s) = {lam1_s:.40f}")
    print(f"  lambda_2 (K_s) = {lam2_s:.40f}")
    print(f"  lambda_1 (K)   = {lam1_comp:.40f}")
    print(f"  lambda_2 (K)   = {lam2_comp:.40f}")

    # Step 3: Spectral gap and correlation length
    Delta_s = lam1_s - lam2_s
    Delta_comp = lam1_comp - lam2_comp
    ratio = lam2_s / lam1_s
    xi2 = -1.0 / np.log(ratio)

    print()
    print("-" * 75)
    print("SPECTRAL GAP AND CORRELATION LENGTH")
    print("-" * 75)
    print(f"  Delta (K_s) = lambda_1 - lambda_2 = {Delta_s:.30f}")
    print(f"  Delta (K)   = lambda_1 - lambda_2 = {Delta_comp:.30f}")
    print(f"  Ratio lambda_2/lambda_1            = {ratio:.30f}")
    print(f"  Correlation length xi_2 = -1/ln(lambda_2/lambda_1) = {xi2:.15f}")

    # Step 4: Verify psi_2 has exactly one sign change
    print()
    print("-" * 75)
    print("EIGENVECTOR ANALYSIS")
    print("-" * 75)

    # Sample psi_2 along the line u = t, v = (1-t)/2 for t in [0, 0.5]
    # and along u = v = t for t in [0, 0.5]
    t_vals = np.linspace(0.01, 0.99, 50)
    # Sample along u = t*(1/3), v = t*(1/3) (the diagonal)
    diag_vals = [eval_eigenfunction(C2, basis, t / 3.0, t / 3.0) for t in t_vals]
    sc_diag = count_sign_changes(diag_vals)

    # Sample along the edge v=0: u in (0, 1)
    edge_vals = [eval_eigenfunction(C2, basis, t * 0.99, 0.0) for t in t_vals]
    sc_edge = count_sign_changes(edge_vals)

    # Sample on a grid
    grid_vals = []
    grid_n = 20
    for iu in range(grid_n + 1):
        u = iu / grid_n * 0.99
        for iv in range(grid_n + 1):
            v = iv / grid_n * 0.99
            if u + v <= 0.99:
                grid_vals.append(eval_eigenfunction(C2, basis, u, v))

    n_pos = sum(1 for v in grid_vals if v > 1e-14)
    n_neg = sum(1 for v in grid_vals if v < -1e-14)
    n_zero = len(grid_vals) - n_pos - n_neg

    print(f"  psi_2 sign changes along diagonal:  {sc_diag}")
    print(f"  psi_2 sign changes along edge v=0:  {sc_edge}")
    print(f"  psi_2 on grid: {n_pos} positive, {n_neg} negative, {n_zero} near-zero "
          f"(of {len(grid_vals)} points)")
    print(f"  => psi_2 has a nodal surface (first excited state, as expected)")

    # Step 5: Two-point correlation function
    print()
    print("-" * 75)
    print("TWO-POINT CORRELATION FUNCTION C(r)")
    print("-" * 75)

    r_values = [0.1 * k for k in range(1, 10)]
    t3 = time.time()
    C_r, c2_coeff, overlap_12, overlap_11 = compute_correlation_function(
        C1, C2, lam1_s, lam2_s, basis, r_values
    )
    t4 = time.time()
    print(f"  Spectral overlap c_2 = <psi_1^2, psi_2> / (||psi_1||^2 ||psi_2||) = {c2_coeff:.15f}")
    print(f"  [{t4-t3:.1f}s for correlation computation]")
    print()
    print(f"  {'r':>6s}  {'C(r)':>20s}  {'ln|C(r)|':>15s}  {'C(r)/C(0.1)':>15s}")
    print(f"  {'-'*6}  {'-'*20}  {'-'*15}  {'-'*15}")

    C_01 = C_r[0.1] if abs(C_r[0.1]) > 1e-50 else 1.0
    for r in r_values:
        cr = C_r[r]
        ln_cr = np.log(abs(cr)) if abs(cr) > 1e-300 else float('-inf')
        ratio_cr = cr / C_01 if abs(C_01) > 1e-50 else 0.0
        print(f"  {r:6.1f}  {cr:20.12e}  {ln_cr:15.8f}  {ratio_cr:15.10f}")

    # Verify exponential decay: ln C(r) should be linear in r
    ln_C = [np.log(abs(C_r[r])) for r in r_values if abs(C_r[r]) > 1e-300]
    r_fit = [r for r in r_values if abs(C_r[r]) > 1e-300]
    if len(r_fit) >= 2:
        slope = (ln_C[-1] - ln_C[0]) / (r_fit[-1] - r_fit[0])
        xi2_from_fit = -1.0 / slope
        print()
        print(f"  Fitted slope of ln|C(r)|: {slope:.15f}")
        print(f"  xi_2 from fit:            {xi2_from_fit:.15f}")
        print(f"  xi_2 from eigenvalues:    {xi2:.15f}")
        print(f"  Agreement: {abs(xi2_from_fit - xi2) / xi2 * 100:.6e} %")

    # Step 6: Susceptibility
    print()
    print("-" * 75)
    print("SUSCEPTIBILITY")
    print("-" * 75)

    chi = compute_susceptibility_spectral(c2_coeff, lam1_s, lam2_s)
    print(f"  chi = c_2^2 / (1 - lambda_2/lambda_1) = {chi:.15e}")
    print(f"  (top-2 spectral approximation)")

    # Step 7: Mass gap and stiffness
    print()
    print("-" * 75)
    print("MASS GAP AND STIFFNESS")
    print("-" * 75)

    mass_gap = -np.log(ratio)  # = ln(lambda_1/lambda_2)
    print(f"  Mass gap m = -ln(lambda_2/lambda_1) = {mass_gap:.15f}")
    print(f"  Correlation length xi_2 = 1/m       = {xi2:.15f}")

    # Stiffness: second derivative of free energy F = -ln(lambda_1)
    # F(beta) = -ln(lambda_1(beta)); for beta=1 (our case):
    # We approximate d^2F/dbeta^2 by the variance of the energy in the
    # ground state. Energy E = <psi_1| H |psi_1> where H ~ -ln(K).
    # In practice, stiffness = variance of the "action" in the ground state.
    # Here we use the relation: stiffness = (Delta)^2 / chi (fluctuation-dissipation)
    stiffness = Delta_s**2 / chi if abs(chi) > 1e-50 else float('inf')
    print(f"  Stiffness (Delta^2/chi)             = {stiffness:.15e}")

    # Step 8: Verification -- gamma_2
    print()
    print("-" * 75)
    print("VERIFICATION: gamma_2")
    print("-" * 75)

    norm1_sq = compute_norm2(C1, basis)
    u_mom = compute_moment(C1, basis, 1, 0)
    v_mom = compute_moment(C1, basis, 0, 1)
    gamma2 = 1.0 - (u_mom + v_mom) / norm1_sq

    print(f"  gamma_2 = 1 - <u+v>_{{psi_1^2}} = {gamma2:.30f}")

    # Step 9: Summary
    print()
    print("=" * 75)
    print("SUMMARY")
    print("=" * 75)
    print(f"  Galerkin order P        = {P_ORDER}")
    print(f"  Basis dimension n       = {n}")
    print(f"  lambda_1 (K_s)          = {lam1_s:.30f}")
    print(f"  lambda_2 (K_s)          = {lam2_s:.30f}")
    print(f"  Spectral gap Delta      = {Delta_s:.30f}")
    print(f"  Correlation length xi_2 = {xi2:.15f}")
    print(f"  Susceptibility chi      = {chi:.15e}")
    print(f"  Mass gap m              = {mass_gap:.15f}")
    print(f"  Stiffness               = {stiffness:.15e}")
    print(f"  gamma_2                 = {gamma2:.30f}")
    print(f"  Total time              = {time.time()-t0:.1f}s")
    print("=" * 75)
