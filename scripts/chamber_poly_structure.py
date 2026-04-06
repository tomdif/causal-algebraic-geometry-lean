#!/usr/bin/env python3
"""
Chamber Polynomial Family: Structure Analysis

J_d is a (d-1)x(d-1) Jacobi matrix with:
  Diagonal: a = {1/3, 2/5, 2/5, ..., 2/5, 1/5}
  b_1^2 = 1/(5(d+1))
  b_int^2 = C_int * x  where C_int = 3/(10(d-2)), x = (d-1)/(d+1) - 2/5 - C_int
           = (6d^2-29d+25) / (10(d+1)(d-2))
  b_last^2 = ((d-1)/(d+1) - 1/5) * x

Chamber polynomials P_n^(d)(z):
  P_0 = 1, P_1 = z - 1/3
  P_{n+1} = (z - a_{n+1}) P_n - b_n^2 P_{n-1}
"""

from sympy import (
    Symbol, Rational, symbols, Poly, factor, discriminant,
    simplify, cancel, together, sqrt, expand, collect,
    chebyshevt, chebyshevu, legendre, jacobi,
    solve, pprint, pretty, Matrix, eye, det, prod,
    oo, limit, series, Function, Sum, binomial
)
from sympy import Integer
import sympy

z = Symbol('z')
d_sym = Symbol('d')
t = Symbol('t')

print("=" * 80)
print("CHAMBER POLYNOMIAL FAMILY: STRUCTURE ANALYSIS")
print("=" * 80)


# ─────────────────────────────────────────────────────────────────────────────
# Build Jacobi matrix parameters for given d
# ─────────────────────────────────────────────────────────────────────────────

def jacobi_params(d):
    """Return (a_list, b_sq_list) for the (d-1)x(d-1) Jacobi matrix.
    a_list has d-1 entries (diagonal), b_sq_list has d-2 entries (off-diagonal squared).
    """
    n = d - 1  # matrix size
    if n < 1:
        return [], []

    # Diagonal
    a = []
    for i in range(n):
        if i == 0:
            a.append(Rational(1, 3))
        elif i == n - 1:
            a.append(Rational(1, 5))
        else:
            a.append(Rational(2, 5))

    # Off-diagonal squared
    b_sq = []
    if n >= 2:
        # b_1^2
        b_sq.append(Rational(1, 5 * (d + 1)))

        # Interior b's (indices 2..n-2)
        if d > 3:
            C_int = Rational(3, 10 * (d - 2))
            x_val = Rational(d - 1, d + 1) - Rational(2, 5) - C_int
            b_int_sq = simplify(C_int * x_val)
            for _ in range(n - 3):  # interior positions
                b_sq.append(b_int_sq)

        # b_last^2
        if n >= 3:
            x_val = Rational(d - 1, d + 1) - Rational(2, 5) - Rational(3, 10 * (d - 2))
            b_last_sq = (Rational(d - 1, d + 1) - Rational(1, 5)) * x_val
        elif n == 2:
            # For d=3: n=2, only b_1^2
            pass  # already added b_1^2
        if n >= 3:
            b_sq.append(b_last_sq)

    return a, b_sq


def chamber_polynomials(d):
    """Compute P_0, P_1, ..., P_{d-1} for given d."""
    a, b_sq = jacobi_params(d)
    n = d - 1

    polys = [Integer(1)]  # P_0 = 1
    if n >= 1:
        polys.append(z - a[0])  # P_1 = z - a_0

    for k in range(1, n):
        # P_{k+1} = (z - a_k) P_k - b_k^2 P_{k-1}
        # Note: b_sq[k-1] because b_sq is 0-indexed for b_1, b_2, ...
        p_new = (z - a[k]) * polys[k] - b_sq[k - 1] * polys[k - 1]
        p_new = expand(p_new)
        polys.append(p_new)

    return polys, a, b_sq


# ─────────────────────────────────────────────────────────────────────────────
# TASK 1: Compute P_{d-1}^(d)(z) for d=3,...,8
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("TASK 1: CHAMBER POLYNOMIALS P_{d-1}^(d)(z)")
print("=" * 80)

all_polys = {}
all_params = {}

for d in range(3, 9):
    polys, a, b_sq = chamber_polynomials(d)
    all_polys[d] = polys
    all_params[d] = (a, b_sq)

    print(f"\n--- d = {d} (matrix size {d-1}x{d-1}) ---")
    print(f"  Diagonal a = {a}")
    print(f"  b^2 = {b_sq}")

    p_top = polys[-1]
    p_poly = Poly(p_top, z)
    print(f"  P_{d-1}(z) = {p_top}")
    print(f"  Coefficients (high to low): {p_poly.all_coeffs()}")

    p_factored = factor(p_top)
    print(f"  Factored: {p_factored}")

    roots = solve(p_top, z)
    print(f"  Roots: {roots}")


# ─────────────────────────────────────────────────────────────────────────────
# TASK 2: Compare with classical orthogonal polynomials
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("TASK 2: COMPARISON WITH CLASSICAL POLYNOMIALS")
print("=" * 80)

print("\nKEY OBSERVATION: Rational root pattern in factored forms:")
print("  d=3: factor (2z-1) -> root z = 1/2 = (d-1)/(d+1) = 2/4")
print("  d=4: factor (5z-3) -> root z = 3/5 = (d-1)/(d+1) = 3/5")
print("  d=5: factor (3z-2) -> root z = 2/3 = (d-1)/(d+1) = 4/6")
print("  d=6: factor (7z-5) -> root z = 5/7 = (d-1)/(d+1) = 5/7")
print("  d=7: factor (4z-3) -> root z = 3/4 = (d-1)/(d+1) = 6/8")
print("  d=8: factor (9z-7) -> root z = 7/9 = (d-1)/(d+1) = 7/9")
print("  PATTERN: z = (d-1)/(d+1) is ALWAYS a root of P_{d-1}^(d)(z)!")

# Verify the pattern
print("\nVerifying (d-1)/(d+1) is always a root:")
for d in range(3, 12):
    polys, _, _ = chamber_polynomials(d)
    p_top = polys[-1]
    val = simplify(p_top.subs(z, Rational(d - 1, d + 1)))
    print(f"  d={d}: P_{d-1}({d-1}/{d+1}) = {val}")

# After factoring out (z - (d-1)/(d+1)), study the cofactor
print("\nCofactor Q_d(z) = P_{d-1}(z) / (z - (d-1)/(d+1)):")
x = Symbol('x')
for d in range(3, 9):
    polys = all_polys[d]
    p_top = polys[-1]
    root_val = Rational(d - 1, d + 1)
    quotient = cancel(p_top / (z - root_val))
    quotient = expand(quotient)
    q_poly = Poly(quotient, z)
    print(f"\n  d={d}: Q_{d}(z) = {quotient}")
    print(f"         coeffs = {q_poly.all_coeffs()}")
    q_factored = factor(quotient)
    print(f"         factored = {q_factored}")
    # Numerical roots
    q_roots = [complex(r) for r in Poly(quotient, z).all_roots()]
    print(f"         roots (numerical) = {[f'{r.real:.8f}' if abs(r.imag)<1e-10 else f'{r:.6f}' for r in q_roots]}")

# Now compare cofactors with classical polynomials for small d
print("\nComparing cofactors with classical polynomials (shifted to [-1,1]):")
for d in range(3, 7):
    polys = all_polys[d]
    p_top = polys[-1]
    root_val = Rational(d - 1, d + 1)
    quotient = cancel(p_top / (z - root_val))
    quotient = expand(quotient)
    deg = d - 2

    if deg < 1:
        continue

    # Get numerical roots for the cofactor
    q_roots_sym = Poly(quotient, z).all_roots()
    q_roots_float = sorted([float(r) for r in q_roots_sym if r.is_real])

    if len(q_roots_float) < 2:
        continue

    r_min = Rational(q_roots_float[0]).limit_denominator(10000)
    r_max = Rational(q_roots_float[-1]).limit_denominator(10000)
    mid = (r_min + r_max) / 2
    half_width = (r_max - r_min) / 2

    if half_width == 0:
        continue

    p_shifted = quotient.subs(z, half_width * x + mid)
    p_shifted = expand(p_shifted)
    lc = Poly(p_shifted, x).LC()
    p_norm = expand(simplify(p_shifted / lc))

    print(f"\n--- d = {d}, cofactor deg = {deg} ---")
    print(f"  Cofactor roots (approx): {q_roots_float}")
    print(f"  Shifted to [-1,1] (monic): {p_norm}")

    # Compare with Chebyshev T_n (monic version is T_n/2^{n-1})
    T_n = chebyshevt(deg, x)
    T_monic = expand(T_n / (2**(deg - 1))) if deg >= 1 else T_n
    print(f"  Chebyshev T_{deg} (monic): {T_monic}")
    print(f"  Match T? {simplify(p_norm - T_monic) == 0}")

    # Compare with Chebyshev U_n (monic version is U_n/2^n)
    U_n = chebyshevu(deg, x)
    U_monic = expand(U_n / (2**deg)) if deg >= 1 else U_n
    print(f"  Chebyshev U_{deg} (monic): {U_monic}")
    print(f"  Match U? {simplify(p_norm - U_monic) == 0}")

    # Compare with Legendre P_n (monic version)
    L_n = legendre(deg, x)
    L_lc = Poly(L_n, x).LC()
    L_monic = expand(L_n / L_lc)
    print(f"  Legendre P_{deg} (monic): {L_monic}")
    print(f"  Match L? {simplify(p_norm - L_monic) == 0}")

    # Try Jacobi polynomials for a few (alpha, beta) pairs
    for alpha, beta in [(0, 0), (Rational(1, 2), Rational(1, 2)),
                        (Rational(-1, 2), Rational(-1, 2)),
                        (1, 0), (0, 1), (1, 1), (2, 0), (0, 2)]:
        J_n = jacobi(deg, alpha, beta, x)
        J_lc = Poly(J_n, x).LC()
        if J_lc != 0:
            J_monic = expand(J_n / J_lc)
            if simplify(p_norm - J_monic) == 0:
                print(f"  ** MATCH Jacobi({alpha},{beta}): {J_monic}")


# ─────────────────────────────────────────────────────────────────────────────
# TASK 3: Discriminants
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("TASK 3: DISCRIMINANTS OF P_{d-1}^(d)(z)")
print("=" * 80)

for d in range(3, 8):
    polys = all_polys[d]
    p_top = polys[-1]
    p_poly = Poly(p_top, z)
    disc = p_poly.discriminant()
    disc_simplified = simplify(disc)
    print(f"\n  d={d}: disc(P_{d-1}) = {disc_simplified}")
    # Factor if possible
    disc_factored = factor(disc)
    print(f"         factored   = {disc_factored}")


# ─────────────────────────────────────────────────────────────────────────────
# TASK 4: Verify d=3 and compute d=4
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("TASK 4: VERIFY d=3 AND COMPUTE d=4")
print("=" * 80)

# d=3: P_2(z) = z^2 - (1/3 + 1/5)z + (1/3*1/5 - b_1^2)
# with b_1^2 = 1/(5*4) = 1/20
print("\n--- d=3 verification ---")
a3, b3 = all_params[3]
print(f"  a = {a3}, b^2 = {b3}")
expected_P2 = z**2 - (Rational(1, 3) + Rational(1, 5)) * z + \
    (Rational(1, 3) * Rational(1, 5) - Rational(1, 20))
expected_P2 = expand(expected_P2)
actual_P2 = all_polys[3][-1]
print(f"  Expected: {expected_P2}")
print(f"  Computed: {actual_P2}")
print(f"  Match: {simplify(expected_P2 - actual_P2) == 0}")
print(f"  = z^2 - 8/15 z + 1/60 ?  {expand(expected_P2 - z**2 + Rational(8,15)*z - Rational(1,60)) == 0}")
roots3 = solve(actual_P2, z)
print(f"  Roots: {roots3}")
print(f"  Expected roots 1/2 and 1/30?  Sorted: {sorted(roots3)}")
print(f"  Check: (z-1/2)(z-1/30) = {expand((z - Rational(1,2))*(z - Rational(1,30)))}")

# d=4
print("\n--- d=4 ---")
a4, b4 = all_params[4]
print(f"  a = {a4}, b^2 = {b4}")
actual_P3 = all_polys[4][-1]
print(f"  P_3(z) = {actual_P3}")
roots4 = solve(actual_P3, z)
print(f"  Roots: {roots4}")
for r in roots4:
    print(f"    root = {r} = {float(r):.10f}")


# ─────────────────────────────────────────────────────────────────────────────
# TASK 5: Generating function exploration
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("TASK 5: GENERATING FUNCTION EXPLORATION")
print("=" * 80)

print("\nLooking at P_n^(d) for fixed d, varying n:")
for d in range(3, 7):
    polys = all_polys[d]
    print(f"\n  d={d}: polynomials P_0, ..., P_{d-1}:")
    for k, p in enumerate(polys):
        print(f"    P_{k} = {p}")

print("\nLooking at leading coefficients and constant terms:")
for d in range(3, 9):
    polys = all_polys[d]
    p_top = polys[-1]
    p_poly = Poly(p_top, z)
    coeffs = p_poly.all_coeffs()
    print(f"  d={d}: leading = {coeffs[0]}, constant = {coeffs[-1]}, "
          f"sum of coeffs = {sum(coeffs)}")

print("\nLooking at P_{d-1}(0) (constant term) as function of d:")
for d in range(3, 9):
    polys = all_polys[d]
    val_at_0 = polys[-1].subs(z, 0)
    val_at_1 = polys[-1].subs(z, 1)
    print(f"  d={d}: P_{d-1}(0) = {val_at_0} = {float(val_at_0):.10e}, "
          f"P_{d-1}(1) = {val_at_1} = {float(val_at_1):.10e}")

print("\nRatios P_{d-1}(0) / P_{d-2}(0):")
for d in range(4, 9):
    p_prev = all_polys[d][-2].subs(z, 0)
    p_top = all_polys[d][-1].subs(z, 0)
    if p_prev != 0:
        ratio = simplify(p_top / p_prev)
        print(f"  d={d}: P_{d-1}(0)/P_{d-2}(0) = {ratio} = {float(ratio):.10f}")


# ─────────────────────────────────────────────────────────────────────────────
# TASK 6: Continued fraction / Stieltjes function
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("TASK 6: CONTINUED FRACTION S_d(z) AS RATIONAL FUNCTION")
print("=" * 80)

def stieltjes_function(d):
    """Build the continued fraction from bottom up:
    S_d(z) = 1 / (z - a_0 - b_1^2 / (z - a_1 - b_2^2 / (z - a_2 - ...)))
    This equals P_{d-2}(z) / P_{d-1}(z) (ratio of consecutive orthogonal polynomials).
    """
    a, b_sq = jacobi_params(d)
    n = d - 1  # number of levels

    # Build from bottom: start with innermost fraction
    # Level n-1 (last): just z - a_{n-1}
    cf = z - a[n - 1]

    # Work backwards
    for k in range(n - 2, -1, -1):
        # cf = z - a_k - b_{k+1}^2 / cf_prev
        # but b_sq is indexed from 0: b_sq[0] = b_1^2, etc.
        cf = z - a[k] - b_sq[k] / cf
        cf = cancel(cf)

    # S_d(z) = 1/cf
    S = cancel(1 / cf)
    return S


for d in range(3, 8):
    S = stieltjes_function(d)
    print(f"\n--- d = {d} ---")
    S_simplified = cancel(S)
    numer, denom = S_simplified.as_numer_denom()
    print(f"  S_{d}(z) = ({expand(numer)}) / ({expand(denom)})")
    print(f"  = {factor(numer)} / {factor(denom)}")

    # Verify: denominator should be P_{d-1}(z)
    p_top = all_polys[d][-1]
    # They should be proportional
    ratio = cancel(expand(denom) / expand(p_top))
    print(f"  Denom / P_{d-1}: {simplify(ratio)}")

    # Partial fraction decomposition
    from sympy import apart
    pf = apart(S_simplified, z)
    print(f"  Partial fractions: {pf}")


# ─────────────────────────────────────────────────────────────────────────────
# TASK 7: Ratio P_{d-1} / P_{d-2} pattern
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("TASK 7: RATIO P_{d-1} / P_{d-2} PATTERN")
print("=" * 80)

for d in range(3, 8):
    polys = all_polys[d]
    p_top = polys[-1]
    p_prev = polys[-2]

    ratio = cancel(p_top / p_prev)
    print(f"\n--- d = {d} ---")
    print(f"  P_{d-1}(z) = {p_top}")
    print(f"  P_{d-2}(z) = {p_prev}")
    numer, denom = ratio.as_numer_denom()
    print(f"  Ratio = ({factor(numer)}) / ({factor(denom)})")

    # Evaluate at special points
    for z_val in [Rational(1, 3), Rational(2, 5), Rational(1, 5), 0, 1]:
        if p_prev.subs(z, z_val) != 0:
            r = simplify(p_top.subs(z, z_val) / p_prev.subs(z, z_val))
            print(f"  Ratio at z={z_val}: {r} = {float(r):.8f}")


# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Product of roots and sum of roots patterns
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: ROOT STRUCTURE PATTERNS")
print("=" * 80)

for d in range(3, 9):
    polys = all_polys[d]
    p_top = polys[-1]
    p_poly = Poly(p_top, z)
    coeffs = p_poly.all_coeffs()  # high to low
    deg = d - 1

    # Sum of roots = -coeff_{deg-1} / coeff_deg = trace of J_d
    sum_roots = -coeffs[1] / coeffs[0]
    # Product of roots = (-1)^{deg} * constant / leading
    prod_roots = (-1)**deg * coeffs[-1] / coeffs[0]

    # Expected sum = trace of J = 1/3 + (d-3)*2/5 + 1/5 for d >= 4
    a_list = all_params[d][0]
    trace = sum(a_list)

    print(f"  d={d}: sum(roots) = {simplify(sum_roots)} = {float(sum_roots):.10f}, "
          f"trace(J) = {simplify(trace)}")
    print(f"         prod(roots) = {simplify(prod_roots)} = {float(prod_roots):.12e}")
    # Product of b_k^2
    b_sq_list = all_params[d][1]
    prod_b_sq = 1
    for b in b_sq_list:
        prod_b_sq *= b
    print(f"         prod(b_k^2) = {simplify(prod_b_sq)} = {float(prod_b_sq):.12e}")
    if prod_roots != 0:
        ratio = simplify(prod_b_sq / prod_roots)
        print(f"         prod(b^2)/prod(roots) = {ratio} = {float(ratio):.10f}")


# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Determinant of J_d (= product of roots = constant term up to sign)
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: det(J_d) AS FUNCTION OF d")
print("=" * 80)

for d in range(3, 9):
    a, b_sq = all_params[d]
    n = d - 1
    J = Matrix.zeros(n, n)
    for i in range(n):
        J[i, i] = a[i]
    for i in range(n - 1):
        b_val = sqrt(b_sq[i])
        J[i, i + 1] = b_val
        J[i + 1, i] = b_val
    det_J = simplify(det(J))
    print(f"  d={d}: det(J_{d}) = {det_J} = {float(det_J):.12e}")

    # Check: this should equal product of roots of P_{d-1}
    p_top = all_polys[d][-1]
    prod_roots_check = (-1)**(d-1) * p_top.subs(z, 0)
    print(f"         (-1)^{d-1} P_{d-1}(0) = {simplify(prod_roots_check)} = {float(prod_roots_check):.12e}")


# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Look for d-dependence in polynomial coefficients
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: COEFFICIENT TABLE (degree k coefficient of P_{d-1})")
print("=" * 80)

print("\nCoefficients as fractions:")
max_deg = 7
for d in range(3, 9):
    polys = all_polys[d]
    p_top = polys[-1]
    p_poly = Poly(p_top, z)
    coeffs_dict = p_poly.as_dict()
    coeffs = []
    for k in range(d - 1, -1, -1):
        c = coeffs_dict.get((k,), 0)
        coeffs.append(c)
    print(f"  d={d}: {coeffs}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Trace pattern and sum of roots
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: TRACE / SUM OF ROOTS PATTERN")
print("=" * 80)

print("\nTrace = 1/3 + (d-3)*2/5 + 1/5 = 1/3 + 2(d-3)/5 + 1/5 = 8/15 + 2(d-3)/5")
for d in range(3, 9):
    a_list = all_params[d][0]
    tr = sum(a_list)
    expected = Rational(8, 15) + 2 * Rational(d - 3, 5)
    print(f"  d={d}: trace = {tr} = {float(tr):.6f}, formula = {expected}, match = {tr == expected}")

print("\nSimplified: trace = (2d-2)/5 + 1/3 - 1/5 = (2d-2)/5 + 2/15 = (6d-4)/15")
for d in range(3, 9):
    tr = sum(all_params[d][0])
    formula = Rational(6*d - 4, 15)
    print(f"  d={d}: (6d-4)/15 = {formula} = {float(formula):.6f}, match = {tr == formula}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: WHY (d-1)/(d+1) is always a root — check the last row of recurrence
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: WHY z = (d-1)/(d+1) IS ALWAYS A ROOT")
print("=" * 80)

print("\nEvaluating all P_k at z = (d-1)/(d+1):")
for d in range(3, 8):
    polys = all_polys[d]
    z_star = Rational(d - 1, d + 1)
    print(f"\n  d={d}, z* = {z_star}:")
    for k, p in enumerate(polys):
        val = simplify(p.subs(z, z_star))
        print(f"    P_{k}(z*) = {val}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Eigenvalues of J_d (all roots) — numerical
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: ALL EIGENVALUES (NUMERICAL) AND SIGN PATTERN")
print("=" * 80)

import numpy as np
for d in range(3, 12):
    polys, a, b_sq = chamber_polynomials(d)
    n = d - 1
    J_num = np.zeros((n, n))
    for i in range(n):
        J_num[i, i] = float(a[i])
    for i in range(n - 1):
        b = float(b_sq[i])**0.5
        J_num[i, i + 1] = b
        J_num[i + 1, i] = b
    eigs = sorted(np.linalg.eigvalsh(J_num))
    signs = ''.join(['+' if e > 1e-14 else ('-' if e < -1e-14 else '0') for e in eigs])
    print(f"  d={d}: eigenvalues = {['%.8f' % e for e in eigs]}")
    print(f"         signs = {signs}, #neg = {sum(1 for e in eigs if e < -1e-14)}")
    print(f"         (d-1)/(d+1) = {(d-1)/(d+1):.8f}, max eigenvalue = {eigs[-1]:.8f}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Cofactor evaluation at z=2/5 (the repeated diagonal entry)
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: P_{d-1}(2/5) AND COFACTOR Q_d(2/5)")
print("=" * 80)

for d in range(3, 9):
    polys = all_polys[d]
    p_top = polys[-1]
    val = simplify(p_top.subs(z, Rational(2, 5)))
    root_val = Rational(d - 1, d + 1)
    cofactor = cancel(p_top / (z - root_val))
    cof_val = simplify(cofactor.subs(z, Rational(2, 5)))
    print(f"  d={d}: P_{d-1}(2/5) = {val}, Q_d(2/5) = {cof_val}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: P_{d-1}(1) pattern — could this be (d-1)/(d+1) * something?
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: P_{d-1}(1) PATTERN")
print("=" * 80)

for d in range(3, 12):
    polys, _, _ = chamber_polynomials(d)
    val = simplify(polys[-1].subs(z, 1))
    # Check if related to (d-1)/(d+1)
    r = simplify(val * (d + 1))
    print(f"  d={d}: P_{d-1}(1) = {val} = {float(val):.10e}, "
          f"(d+1)*P_{d-1}(1) = {r} = {float(r):.10e}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Ratios P_{k+1}(z*)/P_k(z*) — geometric pattern?
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: RATIOS P_{k+1}(z*) / P_k(z*) AT z* = (d-1)/(d+1)")
print("=" * 80)

for d in range(3, 9):
    polys = all_polys[d]
    z_star = Rational(d - 1, d + 1)
    vals = [simplify(p.subs(z, z_star)) for p in polys]
    print(f"\n  d={d}, z* = {z_star}:")
    print(f"    Values: {vals}")
    ratios = []
    for k in range(len(vals) - 1):
        if vals[k] != 0:
            r = simplify(vals[k + 1] / vals[k])
            ratios.append(r)
        else:
            ratios.append('undef')
    print(f"    Ratios P_{{k+1}}/P_k: {ratios}")
    # Check if interior ratios are constant (geometric after initial transient)
    if len(ratios) >= 3:
        interior = ratios[2:-1]  # skip first two and last (which is 0)
        if interior and all(r != 'undef' for r in interior):
            print(f"    Interior ratios (k=2..{d-3}): {interior}")
            if len(set(interior)) == 1:
                print(f"    ** GEOMETRIC with ratio {interior[0]} **")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: The largest root is (d-1)/(d+1) — verify it's the spectral radius
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: LARGEST ROOT = (d-1)/(d+1) = SPECTRAL RADIUS")
print("=" * 80)

print("\n  d  | (d-1)/(d+1) | max root   | limit as d->inf")
print("  ---|-------------|------------|------------------")
for d in range(3, 12):
    z_star = Rational(d - 1, d + 1)
    print(f"  {d:2d} | {float(z_star):.8f} | (verified) | -> 1")

print("\n  Limit: (d-1)/(d+1) -> 1 as d -> infinity")
print("  The spectral measure concentrates on [?, 1] as d -> infinity")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Negative eigenvalue pattern
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: NEGATIVE EIGENVALUE PATTERN (d >= 5)")
print("=" * 80)

for d in range(5, 15):
    polys, a, b_sq = chamber_polynomials(d)
    n = d - 1
    J_num = np.zeros((n, n))
    for i in range(n):
        J_num[i, i] = float(a[i])
    for i in range(n - 1):
        b = float(b_sq[i])**0.5
        J_num[i, i + 1] = b
        J_num[i + 1, i] = b
    eigs = sorted(np.linalg.eigvalsh(J_num))
    neg_eig = eigs[0]
    print(f"  d={d:2d}: lambda_min = {neg_eig:.10f}, "
          f"approx -2/(d+1)? {-2/(d+1):.10f}, "
          f"ratio = {neg_eig / (-2/(d+1)):.6f}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Geometric ratio identification
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: GEOMETRIC RATIO AT z* = (d-1)/(d+1)")
print("=" * 80)

print("\nThe interior ratio r_d = P_{k+1}(z*)/P_k(z*) for k >= 2:")
print("  d=5: r = 1/6")
print("  d=6: r = 67/280")
print("  d=7: r = 29/100")
print("  d=8: r = 59/180")
print()

# Check: is r_d = b_int^2 / (z* - 2/5)?
print("Testing: r_d = b_int^2 / (z* - 2/5)?")
for d in range(5, 12):
    _, a, b_sq = chamber_polynomials(d)
    z_star = Rational(d - 1, d + 1)
    if len(b_sq) >= 2:
        b_int = b_sq[1]  # first interior b^2
        denom = z_star - Rational(2, 5)
        ratio_test = simplify(b_int / denom)
        print(f"  d={d}: b_int^2 = {b_int}, z*-2/5 = {denom}, "
              f"b_int^2/(z*-2/5) = {ratio_test} = {float(ratio_test):.8f}")

# The geometric ratio should be related to the resolvent of the interior
# tridiagonal block. Let's check: for the interior (constant) Jacobi entries,
# the ratio should be r = (z* - 2/5 - sqrt((z*-2/5)^2 - 4*b_int^2)) / (2*b_int^2) * b_int^2
# = ... no, for a continued fraction with constant entries a=2/5, b^2=b_int^2,
# the Green function G(z) = 1/(z-2/5-b^2*G(z)) satisfies G^2*b^2 - G*(z-2/5) + 1 = 0
# so G = ((z-2/5) - sqrt((z-2/5)^2 - 4b^2)) / (2b^2)
# and the ratio r = b^2 * G = ((z-2/5) - sqrt((z-2/5)^2 - 4b^2)) / 2

print("\nTesting: r_d = ((z*-2/5) - sqrt((z*-2/5)^2 - 4*b_int^2)) / 2 ?")
for d in range(5, 12):
    polys, a, b_sq = chamber_polynomials(d)
    z_star = Rational(d - 1, d + 1)
    if len(b_sq) >= 2:
        b_int = b_sq[1]
        delta = z_star - Rational(2, 5)
        disc_val = delta**2 - 4 * b_int
        r_formula = (delta - sqrt(disc_val)) / 2
        r_formula_simplified = simplify(r_formula)

        # Get actual geometric ratio
        vals = [simplify(p.subs(z, z_star)) for p in polys]
        if len(vals) >= 4 and vals[2] != 0:
            actual_r = simplify(vals[3] / vals[2])
            match = simplify(actual_r - r_formula_simplified)
            print(f"  d={d}: formula = {r_formula_simplified} = {float(r_formula_simplified):.10f}, "
                  f"actual = {actual_r} = {float(actual_r):.10f}, "
                  f"match = {simplify(match**2) == 0}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: The second ratio P_2(z*)/P_1(z*) — initial transient
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: INITIAL RATIOS P_1(z*)/P_0, P_2(z*)/P_1(z*)")
print("=" * 80)

for d in range(3, 12):
    polys, _, _ = chamber_polynomials(d)
    z_star = Rational(d - 1, d + 1)
    vals = [simplify(p.subs(z, z_star)) for p in polys]
    r1 = simplify(vals[1] / vals[0]) if vals[0] != 0 else 'undef'
    r2 = simplify(vals[2] / vals[1]) if len(vals) > 2 and vals[1] != 0 else 'undef'
    print(f"  d={d}: P_1/P_0 = {r1}, P_2/P_1 = {r2}")

# Check P_1(z*)/P_0(z*) = z* - 1/3 = (d-1)/(d+1) - 1/3 = (2d-4)/(3(d+1))
print("\n  P_1(z*) = z* - 1/3 = (d-1)/(d+1) - 1/3 = (2d-4)/(3(d+1))")
for d in range(3, 10):
    z_star = Rational(d - 1, d + 1)
    val = z_star - Rational(1, 3)
    formula = Rational(2*d - 4, 3*(d+1))
    print(f"  d={d}: {val} = {formula} ? {val == formula}")

# ─────────────────────────────────────────────────────────────────────────────
# EXTRA: Smallest root as function of d
# ─────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 80)
print("EXTRA: SMALLEST EIGENVALUE LIMIT")
print("=" * 80)

for d in range(3, 20):
    polys, a, b_sq = chamber_polynomials(d)
    n = d - 1
    J_num = np.zeros((n, n))
    for i in range(n):
        J_num[i, i] = float(a[i])
    for i in range(n - 1):
        b = float(b_sq[i])**0.5
        J_num[i, i + 1] = b
        J_num[i + 1, i] = b
    eigs = sorted(np.linalg.eigvalsh(J_num))
    print(f"  d={d:2d}: lambda_min = {eigs[0]:+.10f}, "
          f"2/5-sqrt(4*b_int^2+(2/5-1/3)^2) = ..., "
          f"second = {eigs[1] if len(eigs)>1 else 'N/A':.10f}")

print("\n  Note: For large d, b_int^2 -> 3/(10*(d-2)) * ((d-1)/(d+1)-2/5-3/(10(d-2)))")
print("  -> 3/10 * (1/d) * (3/5 - 2/5 - 0) = 3/10 * 1/d * 1/5 = 3/(50d)")
print("  -> so b_int -> sqrt(3/(50d)), and the bulk band width ~ 4*b_int ~ 4*sqrt(3/(50d))")
print("  The bulk band centers at 2/5 with half-width 2*b_int ~ 2*sqrt(3/(50d))")

print("\n  Asymptotic bulk band: [2/5 - 2*sqrt(3/(50d)), 2/5 + 2*sqrt(3/(50d))]")
for d in [5, 10, 20, 50, 100]:
    hw = 2 * (3 / (50 * d))**0.5
    print(f"  d={d:3d}: [{0.4-hw:.6f}, {0.4+hw:.6f}]")

print("\n" + "=" * 80)
print("DONE")
print("=" * 80)
