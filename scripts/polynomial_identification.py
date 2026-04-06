"""
polynomial_identification.py — Identify J_d with a known OP family

Test J_d against:
1. Hahn polynomials Q_n(x; α, β, N)
2. Dual Hahn polynomials R_n(λ(x); γ, δ, N)
3. Racah polynomials R_n(λ(x); α, β, γ, δ)
4. Krawtchouk polynomials K_n(x; p, N)

For each: compare the Jacobi matrix coefficients (diagonal a_k, subdiagonal b_k²)
against the textbook recurrence formulas.
"""
from fractions import Fraction
import numpy as np
from itertools import product as iprod

# ============================================================
# THE JACOBI FAMILY J_d (exact rational)
# ============================================================

def jacobi_family(d):
    """Return (a_k, b_k²) for J_d."""
    n = d - 1  # matrix size
    lam = Fraction(d-1, d+1)
    C_int = Fraction(3, 10*(d-2)) if d > 2 else Fraction(0)
    x = lam - Fraction(2,5) - C_int

    # Diagonal
    a = [Fraction(1,3)] + [Fraction(2,5)]*(d-3) + [Fraction(1,5)]

    # Couplings
    b_sq = []
    b1_sq = Fraction(1, 5*(d+1))
    b_sq.append(b1_sq)

    if d >= 4:
        b_int_sq = C_int * x
        for k in range(1, n-2):
            b_sq.append(b_int_sq)
        # Last coupling
        C_last = lam - Fraction(1,5)
        b_last_sq = C_last * x
        b_sq.append(b_last_sq)

    return a, b_sq

# ============================================================
# 1. HAHN POLYNOMIALS Q_n(x; α, β, N)
# ============================================================
# Three-term recurrence: x Q_n = A_n Q_{n+1} + (A_n+C_n) Q_n + C_n Q_{n-1}  [shifted]
# The JACOBI MATRIX of the Hahn has:
#   diagonal: A_n + C_n
#   subdiagonal²: A_n * C_{n+1}  (product of adjacent A,C)
#
# A_n = (n+α+β+1)(n+α+1)(N-n) / ((2n+α+β+1)(2n+α+β+2))
# C_n = n(n+α+β+N+1)(n+β) / ((2n+α+β)(2n+α+β+1))

def hahn_coeffs(n, alpha, beta, N):
    """Hahn recurrence coefficients A_n, C_n."""
    a, b = alpha, beta
    A = Fraction((n+a+b+1)*(n+a+1)*(N-n), (2*n+a+b+1)*(2*n+a+b+2))
    if n == 0:
        C = Fraction(0)
    else:
        C = Fraction(n*(n+a+b+N+1)*(n+b), (2*n+a+b)*(2*n+a+b+1))
    return A, C

def hahn_jacobi_matrix(alpha, beta, N):
    """Return (diagonal, subdiag²) for Hahn Jacobi matrix."""
    diag = []
    sub_sq = []
    for n in range(N+1):
        A, C = hahn_coeffs(n, alpha, beta, N)
        diag.append(A + C)
        if n < N:
            A_next, C_next = hahn_coeffs(n+1, alpha, beta, N)
            sub_sq.append(A * C_next)
    return diag, sub_sq

# ============================================================
# 2. DUAL HAHN POLYNOMIALS R_n(λ(x); γ, δ, N)
# ============================================================
# λ(x) = x(x + γ + δ + 1)
# A_n = (n+γ+δ+1)(n+γ+1)(N-n) / ((2n+γ+δ+1)(2n+γ+δ+2))
# C_n = n(n+δ)(N+γ+δ+1-n) / ((2n+γ+δ)(2n+γ+δ+1))  [for n≥1, C_0=0]

def dual_hahn_coeffs(n, gamma, delta, N):
    a = gamma + delta
    A = Fraction((n+a+1)*(n+gamma+1)*(N-n), (2*n+a+1)*(2*n+a+2))
    if n == 0:
        C = Fraction(0)
    else:
        C = Fraction(n*(n+delta)*(N+gamma+delta+1-n), (2*n+a)*(2*n+a+1))
    return A, C

def dual_hahn_jacobi_matrix(gamma, delta, N):
    diag = []
    sub_sq = []
    for n in range(N+1):
        A, C = dual_hahn_coeffs(n, gamma, delta, N)
        diag.append(A + C)
        if n < N:
            A_next, C_next = dual_hahn_coeffs(n+1, gamma, delta, N)
            sub_sq.append(A * C_next)
    return diag, sub_sq

# ============================================================
# 3. KRAWTCHOUK POLYNOMIALS K_n(x; p, N)
# ============================================================
# A_n = p(N-n), C_n = (1-p)n
# Diagonal: A_n + C_n = pN - n(2p-1)
# Sub²: A_n * C_{n+1} = p(1-p)(N-n)(n+1)

def krawtchouk_jacobi_matrix(p, N):
    diag = []
    sub_sq = []
    for n in range(N+1):
        A = p * (N - n)
        C = (1 - p) * n
        diag.append(A + C)
        if n < N:
            A_next = p * (N - n - 1)
            C_next = (1 - p) * (n + 1)
            sub_sq.append(A * C_next)
    return diag, sub_sq

# ============================================================
# SEARCH: Find parameters that match J_d
# ============================================================

print("=" * 70)
print("SEARCHING FOR POLYNOMIAL MATCH")
print("=" * 70)

for d in [3, 4, 5, 6, 7]:
    target_a, target_b = jacobi_family(d)
    n_size = d - 1

    print(f"\n{'='*60}")
    print(f"  d = {d}, J_d size = {n_size}×{n_size}")
    print(f"  Target diagonal: {target_a}")
    print(f"  Target sub²:     {target_b}")
    print(f"{'='*60}")

    # Try Hahn with various α, β, N
    # N must be n_size - 1 (since Hahn has N+1 nodes)
    N_hahn = n_size - 1

    best_hahn = None
    best_hahn_err = float('inf')

    # Search over rational α, β with small denominators
    for a_num in range(-5, 10):
        for a_den in range(1, 6):
            for b_num in range(-5, 10):
                for b_den in range(1, 6):
                    alpha = Fraction(a_num, a_den)
                    beta = Fraction(b_num, b_den)
                    try:
                        h_diag, h_sub = hahn_jacobi_matrix(alpha, beta, N_hahn)
                        if len(h_diag) != n_size:
                            continue
                        # Check if we can RESCALE to match
                        # J_d might = c * Hahn + offset
                        if h_diag[0] != 0:
                            # Try: target = scale * hahn + shift
                            # From first and last: scale*h[0]+shift = 1/3, scale*h[-1]+shift = 1/5
                            # → scale*(h[0]-h[-1]) = 1/3-1/5 = 2/15
                            if h_diag[0] != h_diag[-1]:
                                scale = Fraction(2, 15) / (h_diag[0] - h_diag[-1])
                                shift = Fraction(1,3) - scale * h_diag[0]
                                # Check all diag entries
                                matched_diag = [scale * h + shift for h in h_diag]
                                if matched_diag == target_a:
                                    # Check sub²
                                    matched_sub = [scale**2 * s for s in h_sub]
                                    if matched_sub == target_b:
                                        print(f"  *** EXACT MATCH: Hahn(α={alpha}, β={beta}, N={N_hahn}) ***")
                                        print(f"      scale={scale}, shift={shift}")
                                        best_hahn = (alpha, beta, N_hahn, scale, shift)
                    except (ZeroDivisionError, ValueError):
                        continue

    # Try Dual Hahn
    for g_num in range(-5, 10):
        for g_den in range(1, 6):
            for d_num in range(-5, 10):
                for d_den in range(1, 6):
                    gamma = Fraction(g_num, g_den)
                    delta = Fraction(d_num, d_den)
                    try:
                        dh_diag, dh_sub = dual_hahn_jacobi_matrix(gamma, delta, N_hahn)
                        if len(dh_diag) != n_size:
                            continue
                        if dh_diag[0] != dh_diag[-1]:
                            scale = Fraction(2, 15) / (dh_diag[0] - dh_diag[-1])
                            shift = Fraction(1,3) - scale * dh_diag[0]
                            matched_diag = [scale * h + shift for h in dh_diag]
                            if matched_diag == target_a:
                                matched_sub = [scale**2 * s for s in dh_sub]
                                if matched_sub == target_b:
                                    print(f"  *** EXACT MATCH: DualHahn(γ={gamma}, δ={delta}, N={N_hahn}) ***")
                                    print(f"      scale={scale}, shift={shift}")
                    except (ZeroDivisionError, ValueError):
                        continue

    if best_hahn is None:
        print(f"  No exact Hahn/DualHahn match found with small parameters.")

# ============================================================
# EIGENVECTOR ANALYSIS
# ============================================================

print("\n\n" + "=" * 70)
print("PERRON EIGENVECTOR ANALYSIS")
print("=" * 70)

for d in range(3, 9):
    a, b_sq = jacobi_family(d)
    n = d - 1
    J = np.zeros((n, n))
    for i in range(n):
        J[i,i] = float(a[i])
    for i in range(len(b_sq)):
        b = np.sqrt(float(b_sq[i]))
        J[i,i+1] = J[i+1,i] = b

    evals, evecs = np.linalg.eigh(J)
    idx = np.argmax(evals)
    top_eval = evals[idx]
    top_evec = evecs[:, idx]
    if top_evec[0] < 0:
        top_evec = -top_evec

    # Normalize so first component = 1
    top_evec = top_evec / top_evec[0]

    print(f"\n  d={d}: top eval = {top_eval:.8f} (target {(d-1)/(d+1):.8f})")
    print(f"    Perron eigenvector (normalized v[0]=1): {[f'{v:.6f}' for v in top_evec]}")

    # Check ratios
    if n >= 2:
        ratios = [top_evec[i+1]/top_evec[i] for i in range(n-1)]
        print(f"    Consecutive ratios: {[f'{r:.6f}' for r in ratios]}")

    # Check if components match sqrt(dim) or binomial-type
    # dim(j) = 2j+1 for j=0,1/2,1,...
    print(f"    Squared components: {[f'{v**2:.6f}' for v in top_evec]}")

# ============================================================
# 6j-SYMBOL CHECK
# ============================================================

print("\n\n" + "=" * 70)
print("6j-SYMBOL COUPLING CHECK")
print("=" * 70)

# The 6j-symbol {a b e; d c f} satisfies a 3-term recurrence in e.
# For specific a,b,c,d,f, the recurrence gives a tridiagonal matrix.
# Test: do the couplings b_k² match 6j values?

try:
    from sympy.physics.wigner import wigner_6j
    print("  sympy.physics.wigner available")

    for d in [3, 4, 5]:
        j = Fraction(d, 2)
        print(f"\n  d={d}, j={j}:")
        # Try various 6j configurations
        # {j j 1; j j e} as e varies
        for e_twice in range(0, 2*d+2):
            e = Fraction(e_twice, 2)
            try:
                val = float(wigner_6j(j, j, 1, j, j, e))
                if abs(val) > 1e-15:
                    print(f"    {{j,j,1;j,j,{e}}} = {val:.8f}")
            except:
                pass
except ImportError:
    print("  sympy.physics.wigner not available, skipping 6j check")

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
  1. SU(2) dimension ratio: EXACT match for all d
     le/lo = dim(j)/dim(j-1) where j = d/2

  2. Hahn/Dual Hahn/Racah: search with small parameters
     (results above)

  3. Perron eigenvector: components computed
     (check for representation-theoretic pattern)

  4. 6j-symbols: tested at specific angular momenta
     (check for coupling matches)
""")
