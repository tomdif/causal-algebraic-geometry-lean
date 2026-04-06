"""
Hidden Algebraic Structure Test for Chamber Polynomial Family
=============================================================

Tests whether the Jacobi matrix J_d and position operator N form a
Leonard pair, satisfy Askey-Wilson algebra relations, or exhibit
bispectral properties.

J_d is (d-1)x(d-1) tridiagonal with:
  Diagonal: {1/3, 2/5, ..., 2/5, 1/5}
  b_1^2 = 1/(5(d+1))
  b_int^2 = 3(6d^2 - 29d + 25) / (100(d+1)(d-2)^2)   [all equal interior]
  b_last^2 = 2(2d-3)(6d^2 - 29d + 25) / (50(d+1)^2(d-2))

N = diag(0, 1, 2, ..., d-2)  (position operator)
"""

import numpy as np
from fractions import Fraction
import sys

np.set_printoptions(precision=12, linewidth=120, suppress=True)

# ============================================================
# EXACT (Fraction) construction of J_d
# ============================================================

def build_J_exact(d):
    """Build J_d as a matrix of Fractions."""
    n = d - 1  # matrix size
    if n < 2:
        raise ValueError(f"d={d} gives {n}x{n} matrix, need d >= 4")

    J = [[Fraction(0)] * n for _ in range(n)]

    # Diagonal
    J[0][0] = Fraction(1, 3)
    for i in range(1, n - 1):
        J[i][i] = Fraction(2, 5)
    J[n-1][n-1] = Fraction(1, 5)

    # Couplings (as b^2 values)
    poly_6d = 6*d*d - 29*d + 25  # 6d^2 - 29d + 25

    b1_sq = Fraction(1, 5*(d+1))

    if n >= 3:
        b_int_sq = Fraction(3 * poly_6d, 100*(d+1)*(d-2)**2)
    else:
        b_int_sq = None

    b_last_sq = Fraction(2*(2*d-3)*poly_6d, 50*(d+1)**2*(d-2))

    # Off-diagonal: b_i = sqrt(b_i^2), store as b_i (float for numpy later)
    # For exact work, store b^2 and work with J^2 structure
    # But for the commutator test we need actual J, so use float

    # Build coupling list
    couplings_sq = []
    couplings_sq.append(b1_sq)
    for i in range(1, n - 2):
        couplings_sq.append(b_int_sq)
    if n >= 2:
        couplings_sq.append(b_last_sq)

    return J, couplings_sq


def build_J_float(d):
    """Build J_d as numpy float64 array."""
    n = d - 1
    J = np.zeros((n, n))

    # Diagonal
    J[0, 0] = 1.0/3.0
    for i in range(1, n - 1):
        J[i, i] = 2.0/5.0
    J[n-1, n-1] = 1.0/5.0

    poly_6d = 6*d*d - 29*d + 25

    b1_sq = 1.0 / (5*(d+1))
    b1 = np.sqrt(b1_sq)

    if n >= 3:
        b_int_sq = 3.0 * poly_6d / (100*(d+1)*(d-2)**2)
        b_int = np.sqrt(max(b_int_sq, 0))
    else:
        b_int = 0

    b_last_sq = 2.0*(2*d-3)*poly_6d / (50*(d+1)**2*(d-2))
    b_last = np.sqrt(max(b_last_sq, 0))

    # Off-diagonal
    J[0, 1] = b1
    J[1, 0] = b1
    for i in range(1, n - 2):
        J[i, i+1] = b_int
        J[i+1, i] = b_int
    if n >= 2:
        J[n-2, n-1] = b_last
        J[n-1, n-2] = b_last

    return J


def build_N(d):
    """Build N = diag(0, 1, ..., d-2), size (d-1)x(d-1)."""
    n = d - 1
    return np.diag(np.arange(n, dtype=float))


def commutator(A, B):
    return A @ B - B @ A


def frobenius_norm(M):
    return np.sqrt(np.sum(M**2))


def max_abs(M):
    return np.max(np.abs(M))


# ============================================================
# PRINT UTILITIES
# ============================================================

def print_matrix(name, M, threshold=1e-14):
    """Print matrix, zeroing tiny entries."""
    M_clean = M.copy()
    M_clean[np.abs(M_clean) < threshold] = 0
    print(f"\n{name} ({M.shape[0]}x{M.shape[1]}):")
    for i in range(M.shape[0]):
        row = "  [" + ", ".join(f"{M_clean[i,j]:12.8f}" for j in range(M.shape[1])) + "]"
        print(row)


def print_bandwidth(name, M, threshold=1e-12):
    """Report the bandwidth of M."""
    n = M.shape[0]
    bw = 0
    for i in range(n):
        for j in range(n):
            if abs(M[i, j]) > threshold:
                bw = max(bw, abs(i - j))
    print(f"  Bandwidth of {name}: {bw}")
    return bw


# ============================================================
# TEST 1: [J, N] = K (should be tridiagonal, bandwidth 1)
# ============================================================

def test_commutator_JN(d):
    print(f"\n{'='*60}")
    print(f"  d = {d}  (matrix size {d-1}x{d-1})")
    print(f"{'='*60}")

    J = build_J_float(d)
    N = build_N(d)
    n = d - 1

    print(f"\nJ_d diagonal: {np.diag(J)}")
    print(f"J_d off-diag: {[J[i,i+1] for i in range(n-1)]}")
    print(f"J_d off-diag^2: {[J[i,i+1]**2 for i in range(n-1)]}")

    # K = [J, N]
    K = commutator(J, N)
    print_matrix("K = [J, N]", K)
    bw_K = print_bandwidth("K", K)

    return J, N, K


# ============================================================
# TEST 2: [J, K] and [N, K] -- closure check
# ============================================================

def test_double_commutators(J, N, K, d):
    JK = commutator(J, K)
    NK = commutator(N, K)

    print_matrix("[J, K]", JK)
    bw_JK = print_bandwidth("[J,K]", JK)

    print_matrix("[N, K]", NK)
    bw_NK = print_bandwidth("[N,K]", NK)

    return JK, NK


# ============================================================
# TEST 3: Linear decomposition -- can [J,K], [N,K] be written
#          as linear combos of {I, J, N, JN+NJ, K}?
# ============================================================

def test_closure(J, N, K, JK, NK, d):
    n = d - 1
    I_mat = np.eye(n)
    JN_sym = J @ N + N @ J

    # Basis: I, J, N, JN+NJ, K
    basis_names = ["I", "J", "N", "JN+NJ", "K"]
    basis = [I_mat, J, N, JN_sym, K]

    # Flatten each basis matrix
    basis_flat = np.array([b.flatten() for b in basis]).T  # (n^2) x 5

    for name, target in [("[J,K]", JK), ("[N,K]", NK)]:
        target_flat = target.flatten()
        # Least squares
        coeffs, residuals, rank, sv = np.linalg.lstsq(basis_flat, target_flat, rcond=None)
        reconstruction = sum(c * b for c, b in zip(coeffs, basis))
        error = max_abs(target - reconstruction)

        print(f"\n  Decomposition of {name} in {{I, J, N, JN+NJ, K}}:")
        for c, bn in zip(coeffs, basis_names):
            if abs(c) > 1e-14:
                print(f"    {c:+.10f} * {bn}")
        print(f"    Residual (max abs): {error:.2e}")
        if error < 1e-10:
            print(f"    --> CLOSURE in 5-dim algebra!")
        else:
            print(f"    --> NO closure in 5-dim algebra.")

    # Extended basis: add J^2, N^2, JNJ
    J2 = J @ J
    N2 = N @ N
    JNJ = J @ N @ J

    basis_ext_names = basis_names + ["J^2", "N^2", "JNJ"]
    basis_ext = basis + [J2, N2, JNJ]
    basis_ext_flat = np.array([b.flatten() for b in basis_ext]).T

    print(f"\n  Extended basis: {{I, J, N, JN+NJ, K, J^2, N^2, JNJ}}")
    for name, target in [("[J,K]", JK), ("[N,K]", NK)]:
        target_flat = target.flatten()
        coeffs, residuals, rank, sv = np.linalg.lstsq(basis_ext_flat, target_flat, rcond=None)
        reconstruction = sum(c * b for c, b in zip(coeffs, basis_ext))
        error = max_abs(target - reconstruction)

        print(f"\n  Decomposition of {name} in extended basis:")
        for c, bn in zip(coeffs, basis_ext_names):
            if abs(c) > 1e-14:
                print(f"    {c:+.10f} * {bn}")
        print(f"    Residual (max abs): {error:.2e}")
        if error < 1e-10:
            print(f"    --> CLOSURE in 8-dim algebra!")
        else:
            print(f"    --> NO closure in 8-dim algebra.")


# ============================================================
# TEST 4: TD (Tridiagonal) relation for Leonard pair
#   [J, [J, [J, N]]] = alpha * [J, N]
# ============================================================

def test_TD_relation(J, N, K, d):
    JJK = commutator(J, commutator(J, K))  # [J, [J, K]] = [J, [J, [J, N]]]
    # This is [J, [J, [J, N]]] since K = [J, N]

    print(f"\n  TD relation test: [J, [J, [J, N]]] = alpha * [J, N]?")

    # Check if JJK = alpha * K
    # Find best alpha via least squares on flattened
    K_flat = K.flatten()
    JJK_flat = JJK.flatten()

    K_norm_sq = np.dot(K_flat, K_flat)
    if K_norm_sq > 1e-30:
        alpha = np.dot(JJK_flat, K_flat) / K_norm_sq
        residual = JJK - alpha * K
        rel_error = frobenius_norm(residual) / frobenius_norm(JJK) if frobenius_norm(JJK) > 1e-30 else float('inf')

        print(f"    Best alpha = {alpha:.12f}")
        print(f"    |[J,[J,[J,N]]] - alpha*[J,N]| / |[J,[J,[J,N]]]| = {rel_error:.2e}")
        if rel_error < 1e-10:
            print(f"    --> TD(J) SATISFIED with alpha = {alpha:.12f}")
        else:
            print(f"    --> TD(J) FAILS")

            # Check if [J,[J,[J,N]]] = alpha*[J,N] + beta*J + gamma*I + ...
            # i.e., lies in span of {K, J, I, N, JN+NJ}
            n = d - 1
            basis = [K, J, np.eye(n), N, J@N + N@J]
            bnames = ["[J,N]", "J", "I", "N", "JN+NJ"]
            basis_flat = np.array([b.flatten() for b in basis]).T
            coeffs, _, _, _ = np.linalg.lstsq(basis_flat, JJK_flat, rcond=None)
            recon = sum(c*b for c, b in zip(coeffs, basis))
            err = max_abs(JJK - recon)
            print(f"    Decomposition of [J,[J,[J,N]]] in {{[J,N], J, I, N, JN+NJ}}:")
            for c, bn in zip(coeffs, bnames):
                if abs(c) > 1e-14:
                    print(f"      {c:+.12f} * {bn}")
            print(f"    Residual: {err:.2e}")
    else:
        print(f"    K = 0 (degenerate)")

    # Also test [N, [N, [N, J]]] = beta * [N, J]
    NJ = commutator(N, J)
    NNJ = commutator(N, commutator(N, NJ))

    NJ_flat = NJ.flatten()
    NNJ_flat = NNJ.flatten()
    NJ_norm_sq = np.dot(NJ_flat, NJ_flat)
    if NJ_norm_sq > 1e-30:
        beta = np.dot(NNJ_flat, NJ_flat) / NJ_norm_sq
        residual = NNJ - beta * NJ
        rel_error = frobenius_norm(residual) / frobenius_norm(NNJ) if frobenius_norm(NNJ) > 1e-30 else float('inf')

        print(f"\n  TD relation test: [N, [N, [N, J]]] = beta * [N, J]?")
        print(f"    Best beta = {beta:.12f}")
        print(f"    Relative error = {rel_error:.2e}")
        if rel_error < 1e-10:
            print(f"    --> TD(N) SATISFIED with beta = {beta:.12f}")
        else:
            print(f"    --> TD(N) FAILS")


# ============================================================
# TEST 5: Bispectral property
#   Chamber polynomials P_k(lambda_j) form a matrix.
#   Check if columns satisfy a 3-term recurrence.
# ============================================================

def test_bispectral(J, d):
    n = d - 1

    # Eigenvalues and eigenvectors of J
    eigenvalues, eigenvectors = np.linalg.eigh(J)
    print(f"\n  Eigenvalues of J_{d}: {eigenvalues}")

    # The chamber polynomials P_k(x) satisfy:
    #   b_k P_{k+1}(x) + a_k P_k(x) + b_{k-1} P_{k-1}(x) = x P_k(x)
    # with P_0 = 1, P_1 = (x - a_0)/b_0
    #
    # The eigenvectors give P_k(lambda_j) (up to normalization).
    # Eigenvectors from eigh are columns: eigenvectors[:, j] is the j-th eigenvector.
    # Component k of eigenvector j is proportional to P_k(lambda_j).

    # Normalize so P_0 = 1
    P = eigenvectors.copy()
    for j in range(n):
        if abs(P[0, j]) > 1e-15:
            P[:, j] /= P[0, j]
        else:
            print(f"    WARNING: P_0(lambda_{j}) ~ 0")

    print(f"\n  P_k(lambda_j) matrix (rows=k, cols=j):")
    print_matrix("P", P)

    # DUAL RECURRENCE: Check if columns satisfy 3-term recurrence in j.
    # For each k, check: does the sequence P_k(lambda_0), P_k(lambda_1), ...
    # satisfy a 3-term recurrence in j?
    # Equivalently: does the TRANSPOSE P^T have a tridiagonal structure?
    # i.e., does P^T = Q * diag(eigenvalues of dual) * Q^{-1} for tridiagonal Q?

    # More directly: check if there exist alpha_j, beta_j such that
    # for each k: beta_{j-1} P_k(lambda_{j-1}) + alpha_j P_k(lambda_j) + beta_j P_k(lambda_{j+1}) = mu_k P_k(lambda_j)
    # This means P^T * J_dual = diag(mu) * P^T for some tridiagonal J_dual.

    # Check: is P^{-1} * diag(eigenvalues) * P tridiagonal?
    # Wait, that's just J itself. The dual question is different.

    # The dual recurrence: rows of P (indexed by k) are eigenvectors of what?
    # If P_k(lambda_j) are the (k,j) entries, then J * P = P * diag(lambda)
    # For dual: is there a matrix M such that P * M = diag(mu) * P?
    # i.e., M = P^{-1} * diag(mu) * P where mu_k are "dual eigenvalues"

    # Actually for bispectrality we want:
    # There exists a tridiagonal matrix J* acting on the eigenvalue index j such that
    # P * J* = L * P for some diagonal L (the dual eigenvalues).

    # Equivalently: P * J* is diagonal * P, so J* = P^{-1} * L * P.
    # If J* is tridiagonal, we have bispectrality.

    # Let's try: form P^{-1} and check what structure P^{-1} * diag(k) * P has
    # where diag(k) = diag(0, 1, ..., n-1) acts as position in k-space.

    try:
        P_inv = np.linalg.inv(P)
    except np.linalg.LinAlgError:
        print("    P is singular, cannot test bispectrality")
        return None

    # J* = P^{-1} * diag(0,1,...,n-1) * P  (this would be dual to N acting on k-space)
    diag_k = np.diag(np.arange(n, dtype=float))
    J_star = P_inv @ diag_k @ P

    print_matrix("J* = P^{-1} * diag(k) * P", J_star)
    bw = print_bandwidth("J*", J_star, threshold=1e-8)

    if bw <= 1:
        print(f"    --> J* IS TRIDIAGONAL: BISPECTRAL PROPERTY HOLDS!")
    elif bw <= 2:
        print(f"    --> J* has bandwidth 2 (pentadiagonal), NOT strictly bispectral")
    else:
        print(f"    --> J* is dense, NO bispectral property")

    # Also try: P_inv @ diag(lambda) @ P should give J (sanity check)
    diag_lam = np.diag(eigenvalues)
    J_check = P_inv @ diag_lam @ P
    print(f"\n  Sanity: |P^{{-1}} diag(lam) P - J| = {max_abs(J_check - J):.2e}")

    # Try the other direction: is there a tridiagonal action on j-index?
    # Check: for each row k of P, does the sequence P_k(lambda_j) satisfy a 3-term recurrence in j?
    print(f"\n  Testing 3-term recurrence in j for each row k:")
    for k in range(n):
        if n < 3:
            print(f"    k={k}: too few points")
            continue
        # For j=1,...,n-2: check if a_j P_k(lam_{j-1}) + b_j P_k(lam_j) + c_j P_k(lam_{j+1}) = 0
        # with a_j, b_j, c_j independent of k
        # Build system: for each j in 1..n-2, we have one equation per k.
        # If recurrence coefficients are j-dependent but k-independent,
        # then for each j we need: a_j P_k(j-1) + b_j P_k(j) + c_j P_k(j+1) = mu_k * P_k(j)
        pass

    # Simpler approach: compute the "connection matrix" that maps eigenvalue-index vectors
    # For each fixed k, look at row P[k, :]. If all rows satisfy SAME tridiagonal,
    # then the columns of P^T are eigenvectors of that tridiagonal.
    # Equivalently, P^T * (tridiagonal) = (tridiagonal) would mean
    # the ROWS of P are eigenvectors of some matrix.

    # Actually, let's just check: is J_star close to tridiagonal?
    off_tridiag = 0
    for i in range(n):
        for j in range(n):
            if abs(i - j) > 1:
                off_tridiag = max(off_tridiag, abs(J_star[i, j]))
    print(f"\n  Max off-tridiagonal entry of J*: {off_tridiag:.6e}")

    return J_star


# ============================================================
# TEST 6: Dual Jacobi matrix entries
# ============================================================

def report_dual_jacobi(J_star, d):
    if J_star is None:
        return
    n = d - 1
    print(f"\n  Dual Jacobi matrix J* entries for d={d}:")
    print(f"    Diagonal: {[J_star[i,i] for i in range(n)]}")
    if n >= 2:
        print(f"    Upper off-diag: {[J_star[i,i+1] for i in range(n-1)]}")
        print(f"    Lower off-diag: {[J_star[i+1,i] for i in range(n-1)]}")
        # Is it symmetric?
        sym_err = max(abs(J_star[i,i+1] - J_star[i+1,i]) for i in range(n-1))
        print(f"    Symmetry error (|J*_ij - J*_ji|): {sym_err:.2e}")


# ============================================================
# TEST 7: Askey-Wilson algebra test
#   Check q-commutation: [A, A*]_q = qAA* - q^{-1}A*A
# ============================================================

def test_askey_wilson(J, N, K, d):
    n = d - 1
    print(f"\n  Askey-Wilson algebra test for d={d}:")

    # In the Askey-Wilson algebra, we need A and A* where
    # A is diagonal in one basis and A* is tridiagonal, and vice versa.
    # Here J is tridiagonal in the standard basis.
    # A* should be tridiagonal in the eigenbasis of J.

    eigenvalues, U = np.linalg.eigh(J)
    # A = J (tridiagonal in standard basis, diagonal in eigenbasis)
    # A* = U * diag(0,1,...,n-1) * U^T (diagonal in standard basis via position,
    #       tridiagonal in eigenbasis IF bispectral)
    # Actually A* should be N transformed to eigenbasis...
    # Or: A = diag(eigenvalues) in eigenbasis, A* = U^T N U in eigenbasis

    A = J
    A_star = N  # position operator

    # The standard AW relation involves [A, A*]:
    C = commutator(A, A_star)  # = K

    # Check: is there q such that [A, [A, A*]_q] involves A*?
    # The q-commutator: [A, A*]_q = q*A*A* - q^{-1}*A**A
    # For a range of q values, check the AW relation

    # Simpler: check Dolan-Grady relations
    # [A, [A, [A, A*]]] = rho^2 [A, A*]
    # [A*, [A*, [A*, A]]] = rho*^2 [A*, A]

    # This is equivalent to the TD relation already tested above.
    # So let's check the cubic Askey-Wilson relation:
    # A^2 A* - (q + q^{-1}) A A* A + A* A^2 = gamma (A A* + A* A) + rho A* + ...

    # Try to find q such that A^2 A* - beta A A* A + A* A^2 = linear combo of {I, A, A*, AA*+A*A}
    AAstar = A @ A_star
    AstarA = A_star @ A
    A2Astar = A @ A @ A_star
    AstarA2 = A_star @ A @ A
    AAstarA = A @ A_star @ A

    # For each candidate beta, compute A^2A* - beta*A*A*A + A*A^2
    # and check if it lies in span of {I, A, A*, AA*+A*A, K}
    basis = [np.eye(n), A, A_star, AAstar + AstarA, K]
    bnames = ["I", "A", "A*", "AA*+A*A", "[A,A*]"]

    best_beta = None
    best_err = float('inf')

    for beta_trial in np.linspace(-5, 5, 1001):
        LHS = A2Astar - beta_trial * AAstarA + AstarA2
        target_flat = LHS.flatten()
        basis_flat = np.array([b.flatten() for b in basis]).T
        coeffs, _, _, _ = np.linalg.lstsq(basis_flat, target_flat, rcond=None)
        recon = sum(c*b for c, b in zip(coeffs, basis))
        err = max_abs(LHS - recon)
        if err < best_err:
            best_err = err
            best_beta = beta_trial
            best_coeffs = coeffs.copy()

    print(f"    Best beta (q+q^-1) = {best_beta:.6f}")
    print(f"    Residual for A^2A* - beta*AA*A + A*A^2 in {{I,A,A*,AA*+A*A,[A,A*]}}: {best_err:.2e}")

    if best_err < 1e-8:
        # q + q^{-1} = beta => q^2 - beta*q + 1 = 0 => q = (beta +/- sqrt(beta^2 - 4))/2
        disc = best_beta**2 - 4
        if disc >= 0:
            q = (best_beta + np.sqrt(disc)) / 2
            print(f"    q = {q:.10f} (real)")
        else:
            q_re = best_beta / 2
            q_im = np.sqrt(-disc) / 2
            print(f"    q = {q_re:.10f} + {q_im:.10f}i (complex)")
        print(f"    Coefficients:")
        for c, bn in zip(best_coeffs, bnames):
            if abs(c) > 1e-12:
                print(f"      {c:+.10f} * {bn}")
        print(f"    --> ASKEY-WILSON RELATION HOLDS!")
    else:
        print(f"    --> Askey-Wilson relation FAILS at this level")

        # Try extended basis
        basis_ext = basis + [A @ A, A_star @ A_star, A @ A_star @ A]
        bnames_ext = bnames + ["A^2", "A*^2", "AA*A"]
        basis_ext_flat = np.array([b.flatten() for b in basis_ext]).T

        # Now search beta in extended basis
        best_beta2 = None
        best_err2 = float('inf')
        for beta_trial in np.linspace(-5, 5, 1001):
            LHS = A2Astar - beta_trial * AAstarA + AstarA2
            target_flat = LHS.flatten()
            coeffs, _, _, _ = np.linalg.lstsq(basis_ext_flat, target_flat, rcond=None)
            recon = sum(c*b for c, b in zip(coeffs, basis_ext))
            err = max_abs(LHS - recon)
            if err < best_err2:
                best_err2 = err
                best_beta2 = beta_trial
                best_coeffs2 = coeffs.copy()

        print(f"    Extended basis test:")
        print(f"    Best beta = {best_beta2:.6f}, residual = {best_err2:.2e}")
        if best_err2 < 1e-8:
            print(f"    --> AW relation holds in EXTENDED algebra")


# ============================================================
# TEST 8: Exact fraction computations for small d
# ============================================================

def test_exact_fractions(d):
    """Compute K = [J, N] exactly using fractions."""
    print(f"\n{'='*60}")
    print(f"  EXACT FRACTION COMPUTATION for d={d}")
    print(f"{'='*60}")

    n = d - 1
    J_diag, couplings_sq = build_J_exact(d)

    # We can compute [J, N] exactly.
    # J is symmetric tridiagonal with diagonal a_i and off-diagonal b_i.
    # N = diag(0, 1, ..., n-1)
    # [J, N]_{ij} = sum_k (J_{ik} N_{kj} - N_{ik} J_{kj})
    #             = sum_k (J_{ik} * j * delta_{kj} - i * delta_{ik} * J_{kj})
    #             = j * J_{ij} - i * J_{ij}
    #             = (j - i) * J_{ij}
    # So K_{ij} = (j - i) * J_{ij}

    # This means K is antisymmetric! K_{ij} = (j-i) J_{ij}
    # Since J is tridiagonal, K is tridiagonal with:
    # K_{i,i} = 0 (diagonal is zero)
    # K_{i,i+1} = 1 * J_{i,i+1} = b_i
    # K_{i+1,i} = -1 * J_{i+1,i} = -b_i

    print(f"\n  K = [J, N] has the EXACT form:")
    print(f"  K_{{ij}} = (j - i) * J_{{ij}}")
    print(f"  So K is antisymmetric with K_{{i,i+1}} = b_i, K_{{i+1,i}} = -b_i")

    # Now [J, K]_{ij} = sum_k (J_{ik} K_{kj} - K_{ik} J_{kj})
    # Since J tridiag and K tridiag, [J,K] has bandwidth <= 2.

    # Let's compute [J, K] = [J, [J, N]] explicitly.
    # [J, K]_{ij} = (j-i) is NOT right for double commutator.
    # Let me compute properly.

    # Build numerical J for verification
    J_num = build_J_float(d)
    N_num = build_N(d)
    K_num = commutator(J_num, N_num)

    # Verify K = (j-i)*J
    K_formula = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            K_formula[i, j] = (j - i) * J_num[i, j]
    print(f"  Verification |K - (j-i)*J|: {max_abs(K_num - K_formula):.2e}")

    # [J, K] = [J, (j-i)*J]
    # [J, K]_{pq} = sum_r J_{pr} K_{rq} - K_{pr} J_{rq}
    #             = sum_r J_{pr} (q-r) J_{rq} - (r-p) J_{pr} J_{rq}
    #             = sum_r J_{pr} J_{rq} (q - r - r + p)
    #             = sum_r J_{pr} J_{rq} (p + q - 2r)

    # So [J, K]_{pq} = (p+q) (J^2)_{pq} - 2 (J N J)_{pq}
    # where (JNJ)_{pq} = sum_r J_{pr} r J_{rq}

    J2 = J_num @ J_num
    JNJ = J_num @ N_num @ J_num
    JK_formula = np.zeros((n, n))
    for p in range(n):
        for q in range(n):
            JK_formula[p, q] = (p + q) * J2[p, q] - 2 * JNJ[p, q]

    JK_num = commutator(J_num, K_num)
    print(f"  Verification |[J,K] - ((p+q)J^2 - 2JNJ)|: {max_abs(JK_num - JK_formula):.2e}")

    # This means: [J, K] = D_+ * J^2 - 2 * J * N * J
    # where D_+ is the matrix (D_+)_{pq} = (p+q) delta_{pq}... no, (p+q) acts on all entries.
    # Actually: [J, [J, N]] = {D, J^2} - 2 J N J... hmm let me think.
    # (p+q) J^2_{pq} = p J^2_{pq} + q J^2_{pq} = (N J^2)_{pq} + (J^2 N)_{pq}
    # So [J, K] = N J^2 + J^2 N - 2 J N J

    NJ2_plus_J2N = N_num @ J2 + J2 @ N_num
    JK_formula2 = NJ2_plus_J2N - 2 * JNJ
    print(f"  Identity: [J, [J, N]] = NJ^2 + J^2N - 2JNJ")
    print(f"  Verification: {max_abs(JK_num - JK_formula2):.2e}")

    # Similarly [N, K] = [N, (j-i)*J]
    # [N, K]_{pq} = sum_r N_{pr} K_{rq} - K_{pr} N_{rq}
    #             = p K_{pq} - q K_{pq}   (since N is diagonal)
    #             = (p - q) K_{pq}
    #             = (p - q)(q - p) J_{pq}
    #             = -(p - q)^2 J_{pq}

    NK_num = commutator(N_num, K_num)
    NK_formula = np.zeros((n, n))
    for p in range(n):
        for q in range(n):
            NK_formula[p, q] = -(p - q)**2 * J_num[p, q]
    print(f"\n  Identity: [N, [J, N]] = -(p-q)^2 * J")
    print(f"  Verification: {max_abs(NK_num - NK_formula):.2e}")

    # Since (p-q)^2 for tridiagonal is 0 on diag, 1 on off-diag:
    # [N, K]_{pq} = -J_{pq} for |p-q|=1, 0 for p=q
    # So [N, K] = -(J - diag(J))  i.e., minus the off-diagonal part of J!

    J_offdiag = J_num - np.diag(np.diag(J_num))
    print(f"  Equivalently: [N, K] = -J_offdiag")
    print(f"  Verification: {max_abs(NK_num + J_offdiag):.2e}")

    # Now check [N, K] = -J + diag(J)
    # diag(J) is a diagonal matrix, call it A_diag
    # So [N, K] = -J + A_diag

    # And we need: can [J, K] be expressed in terms of our algebra?
    # [J, K] = NJ^2 + J^2N - 2JNJ
    # This is NOT simply a linear combo of {I, J, N, JN+NJ, K}
    # It involves J^2 and JNJ.

    print(f"\n  ALGEBRAIC IDENTITIES (exact):")
    print(f"    [J, N] = K  (antisymmetric, K_{{i,i+1}} = b_i)")
    print(f"    [N, K] = -J_offdiag = -J + diag(a_0, ..., a_{{n-1}})")
    print(f"    [J, K] = NJ^2 + J^2N - 2JNJ")


# ============================================================
# TEST 9: Refined TD relation check with exact identities
# ============================================================

def test_refined_TD(J, N, d):
    """Using the identity [J, [J, N]] = NJ^2 + J^2N - 2JNJ,
    compute [J, [J, [J, N]]] and check against alpha*[J,N] + corrections."""
    n = d - 1
    K = commutator(J, N)
    JK = commutator(J, K)
    JJK = commutator(J, JK)  # [J, [J, [J, N]]]

    print(f"\n  Refined TD analysis for d={d}:")
    print_matrix("[J,[J,[J,N]]]", JJK)
    print_bandwidth("[J,[J,[J,N]]]", JJK)

    # Check: is [J,[J,[J,N]]] proportional to K = [J,N]?
    K_flat = K.flatten()
    JJK_flat = JJK.flatten()
    if np.dot(K_flat, K_flat) > 1e-30:
        alpha = np.dot(JJK_flat, K_flat) / np.dot(K_flat, K_flat)
        res = JJK - alpha * K
        rel = frobenius_norm(res) / frobenius_norm(JJK) if frobenius_norm(JJK) > 1e-30 else 0
        print(f"    alpha = {alpha:.12f}, relative error = {rel:.6e}")

        if rel > 1e-8:
            # Decompose residual in extended basis
            basis = [K, J, np.eye(n), N]
            bnames = ["K", "J", "I", "N"]
            basis_flat = np.array([b.flatten() for b in basis]).T
            coeffs, _, _, _ = np.linalg.lstsq(basis_flat, JJK_flat, rcond=None)
            recon = sum(c*b for c, b in zip(coeffs, basis))
            err = max_abs(JJK - recon)
            print(f"    In {{K, J, I, N}}: residual = {err:.2e}")
            for c, bn in zip(coeffs, bnames):
                if abs(c) > 1e-12:
                    print(f"      {c:+.12f} * {bn}")

    # Also compute [N,[N,[N,J]]] using the identity [N,K] = -J_offdiag
    NJ = commutator(N, J)  # = -K
    NK = commutator(N, K)  # = -J_offdiag
    NNK = commutator(N, NK)
    # [N,[N,[N,J]]] = [N,[N,-K]] = -[N,[N,K]] = -[N, -J_offdiag] = [N, J_offdiag]
    # = [N, J - diag(J)] = [N, J] = -K (since [N, diag] = 0)
    # Wait: [N, J_offdiag] = [N, J] since [N, diag(J)] = 0
    # So [N, [N, [N, J]]] = -[N, [N, K]] = -[N, -J_offdiag] = [N, J_offdiag] = [N, J] = -K

    NNJ_triple = commutator(N, commutator(N, NJ))
    print(f"\n    [N,[N,[N,J]]] vs -K (= [N,J]):")
    print(f"    |[N,[N,[N,J]]] - (-K)| = {max_abs(NNJ_triple + K):.2e}")

    # So [N,[N,[N,J]]] = [N,J] = -K
    # This means beta = 1 in [N,[N,[N,J]]] = beta * [N,J]
    # TD(N) is ALWAYS satisfied with beta = 1!
    print(f"    --> TD(N) ALWAYS holds with beta = 1 (since N is diagonal, this is automatic)")


# ============================================================
# MAIN
# ============================================================

def main():
    print("=" * 70)
    print("  HIDDEN ALGEBRAIC STRUCTURE TEST")
    print("  Chamber Polynomial Family Jacobi Matrix")
    print("=" * 70)

    # First, exact fraction analysis
    for d in [4, 5, 6]:
        test_exact_fractions(d)

    # Main numerical tests
    results = {}
    for d in [4, 5, 6, 7, 8]:
        J, N, K = test_commutator_JN(d)

        print(f"\n--- Double commutators ---")
        JK, NK = test_double_commutators(J, N, K, d)

        print(f"\n--- Closure test ---")
        test_closure(J, N, K, JK, NK, d)

        print(f"\n--- TD (Leonard pair) relation ---")
        test_TD_relation(J, N, K, d)

        print(f"\n--- Refined TD analysis ---")
        test_refined_TD(J, N, d)

        print(f"\n--- Bispectral test ---")
        J_star = test_bispectral(J, d)

        print(f"\n--- Dual Jacobi matrix ---")
        report_dual_jacobi(J_star, d)

        print(f"\n--- Askey-Wilson algebra test ---")
        test_askey_wilson(J, N, K, d)

        results[d] = {
            'J': J, 'N': N, 'K': K, 'JK': JK, 'NK': NK, 'J_star': J_star
        }

    # ============================================================
    # SUMMARY
    # ============================================================
    print("\n" + "=" * 70)
    print("  SUMMARY OF RESULTS")
    print("=" * 70)

    print("\n  EXACT IDENTITIES (valid for ALL d):")
    print("    [J, N] = K  where K_{ij} = (j-i) J_{ij}  (antisymmetric, tridiagonal)")
    print("    [N, K] = [N, [J, N]] = -J_offdiag = -(J - diag(J))")
    print("    [J, K] = [J, [J, N]] = NJ^2 + J^2N - 2JNJ")
    print("    [N, [N, [N, J]]] = [N, J]  (TD(N) trivially satisfied, beta=1)")

    print("\n  For each d, checking:")
    for d in [4, 5, 6, 7, 8]:
        n = d - 1
        J = results[d]['J']
        N = results[d]['N']
        K = results[d]['K']

        # TD(J) check
        JK = commutator(J, K)
        JJK = commutator(J, JK)
        K_flat = K.flatten()
        JJK_flat = JJK.flatten()
        alpha = np.dot(JJK_flat, K_flat) / np.dot(K_flat, K_flat) if np.dot(K_flat, K_flat) > 0 else 0
        res = JJK - alpha * K
        rel = frobenius_norm(res) / frobenius_norm(JJK) if frobenius_norm(JJK) > 1e-30 else 0

        # Bispectral check
        J_star = results[d]['J_star']
        if J_star is not None:
            off_tri = max(abs(J_star[i,j]) for i in range(n) for j in range(n) if abs(i-j) > 1)
        else:
            off_tri = float('inf')

        td_status = "YES" if rel < 1e-8 else f"NO (rel={rel:.2e})"
        bispec_status = "YES" if off_tri < 1e-8 else f"NO (off-tri={off_tri:.2e})"

        print(f"    d={d}: TD(J) Leonard pair: {td_status}")
        print(f"    d={d}: Bispectral:         {bispec_status}")
        print(f"           alpha={alpha:.8f}")


if __name__ == "__main__":
    main()
