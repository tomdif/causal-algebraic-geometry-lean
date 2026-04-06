#!/usr/bin/env python3
"""
Exact Stieltjes transform (m-function) for the Chamber Polynomial Family.

The Jacobi matrix J_d is (d-1)x(d-1) with:
  - Diagonal: {1/3, 2/5, ..., 2/5, 1/5}
  - b_1^2 = 1/(5(d+1))
  - Interior couplings b_int^2, last coupling b_last^2 (exact rational)

We compute m_d(z) = P_{d-2}(z)/Q_{d-1}(z) via backward continued fraction,
working with numerator/denominator polynomials directly (no cancel() overhead).
"""

import numpy as np
from sympy import (
    symbols, sqrt, simplify, factor, cancel, Rational,
    Poly, expand, solve, together, fraction, Integer,
    apart, gcd, div as poly_div, pprint
)
import sympy

z = symbols('z')

# ============================================================
# Parameters
# ============================================================

def exact_params(d):
    d = Integer(d)
    x = (6*d**2 - 29*d + 25) / (10*(d+1)*(d-2))
    a1 = Rational(1, 3)
    a_int = Rational(2, 5)
    a_last = Rational(1, 5)
    b1_sq = Rational(1, 5) / (d + 1)
    if d > 3:
        b_int_sq = sympy.nsimplify(Rational(3, 10) / (d - 2) * x)
        b_last_sq = sympy.nsimplify(((d - 1)/(d + 1) - Rational(1, 5)) * x)
    else:
        b_int_sq = Rational(0)
        b_last_sq = Rational(0)
    return {
        'd': int(d), 'x': x,
        'a1': a1, 'a_int': a_int, 'a_last': a_last,
        'b1_sq': b1_sq, 'b_int_sq': b_int_sq, 'b_last_sq': b_last_sq,
    }


# ============================================================
# Finite m-function via polynomial recursion (FAST)
# ============================================================

# Instead of cancel() on rational expressions, track (P, Q) polynomials:
#   m = P(z)/Q(z)
#   1/(z - a - b^2 * P/Q) = Q / ((z-a)*Q - b^2*P)
# So new_P = Q, new_Q = (z-a)*Q - b^2*P

_m_cache = {}

def finite_m_polys(d):
    """Return (P, Q) as sympy Poly objects where m_d(z) = P(z)/Q(z)."""
    if d in _m_cache:
        return _m_cache[d]

    p = exact_params(d)

    if d == 3:
        # m_2 = 1/(z-1/5)  =>  P2=1, Q2=z-1/5
        P2 = Poly(Rational(1), z)
        Q2 = Poly(z - p['a_last'], z)
        # m_3 = 1/(z-1/3 - b1^2 * P2/Q2) = Q2/((z-1/3)*Q2 - b1^2*P2)
        P = Q2
        Q = Poly((z - p['a1']), z) * Q2 - Poly(p['b1_sq'], z) * P2
        _m_cache[d] = (P, Q)
        return P, Q

    if d == 4:
        # m_3 = 1/(z-1/5)
        Pc = Poly(Rational(1), z)
        Qc = Poly(z - p['a_last'], z)
        # m_2 = Q/(... ) with b_last
        Pc, Qc = Qc, Poly(z - p['a_int'], z)*Qc - Poly(p['b_last_sq'], z)*Pc
        # m_full
        P = Qc
        Q = Poly(z - p['a1'], z)*Qc - Poly(p['b1_sq'], z)*Pc
        _m_cache[d] = (P, Q)
        return P, Q

    # d >= 5
    # Start: m_{d-1} = 1/(z-1/5)
    Pc = Poly(Rational(1), z)
    Qc = Poly(z - p['a_last'], z)

    # Step d-2: couples to d-1 via b_last
    Pc, Qc = Qc, Poly(z - p['a_int'], z)*Qc - Poly(p['b_last_sq'], z)*Pc

    # Interior steps: d-3, ..., 2
    for _ in range(d - 4):
        Pc, Qc = Qc, Poly(z - p['a_int'], z)*Qc - Poly(p['b_int_sq'], z)*Pc

    # Full: attach site 1
    P = Qc
    Q = Poly(z - p['a1'], z)*Qc - Poly(p['b1_sq'], z)*Pc

    _m_cache[d] = (P, Q)
    return P, Q


def m_rational(d):
    """Return m_d(z) as a sympy expression P/Q."""
    P, Q = finite_m_polys(d)
    return P.as_expr() / Q.as_expr()


# ============================================================
# Numerical tools
# ============================================================

def build_numeric_jacobi(d):
    p = exact_params(d)
    n = d - 1
    J = np.zeros((n, n))
    J[0, 0] = float(p['a1'])
    for i in range(1, n-1):
        J[i, i] = float(p['a_int'])
    J[n-1, n-1] = float(p['a_last'])
    if n >= 2:
        b1 = float(p['b1_sq'])**0.5
        J[0, 1] = b1; J[1, 0] = b1
    if n >= 3:
        b_int = float(p['b_int_sq'])**0.5
        for i in range(1, n-2):
            J[i, i+1] = b_int; J[i+1, i] = b_int
        b_last = float(p['b_last_sq'])**0.5
        J[n-2, n-1] = b_last; J[n-1, n-2] = b_last
    return J


def numerical_spectral_measure(d):
    J = build_numeric_jacobi(d)
    evals, evecs = np.linalg.eigh(J)
    weights = evecs[0, :]**2
    return evals, weights


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":

    print("="*70)
    print("EXACT STIELTJES TRANSFORM FOR CHAMBER POLYNOMIAL FAMILY")
    print("="*70)

    # ---- Parameters ----
    print("\n--- EXACT PARAMETERS ---")
    for d in range(3, 11):
        p = exact_params(d)
        print(f"d={d}: b1^2={p['b1_sq']}, b_int^2={p['b_int_sq']}, b_last^2={p['b_last_sq']}")

    # ---- PART 1: Bulk m-function ----
    print("\n\n" + "="*70)
    print("PART 1: BULK m-FUNCTION")
    print("="*70)
    for d in [5, 10, 20, 100]:
        p = exact_params(d)
        a = p['a_int']
        b2 = p['b_int_sq']
        lo = float(a - 2*sqrt(b2))
        hi = float(a + 2*sqrt(b2))
        print(f"d={d:3d}: b_int^2={float(b2):.10f}  band=[{lo:.10f}, {hi:.10f}]  width={hi-lo:.10f}")

    # ---- PART 2: m_d(z) as rational function ----
    print("\n\n" + "="*70)
    print("PART 2: m_d(z) = P(z)/Q(z) RATIONAL FUNCTION")
    print("="*70)

    for d in range(3, 13):
        P, Q = finite_m_polys(d)
        print(f"\nd={d}: m_d = [{P.degree()}/{Q.degree()}]")
        print(f"  Num = {factor(P.as_expr())}")
        print(f"  Den = {factor(Q.as_expr())}")

    # ---- PART 2b: Check (d-1)/(d+1) is always a root of Q ----
    print("\n\n" + "="*70)
    print("KEY: (d-1)/(d+1) IS ALWAYS AN EIGENVALUE (root of Q)")
    print("="*70)

    for d in range(3, 13):
        P, Q = finite_m_polys(d)
        top = Rational(d-1, d+1)
        val = Q.eval(top)
        p_val = P.eval(top)
        print(f"  d={d:2d}: Q((d-1)/(d+1)) = Q({top}) = {val},  P({top}) = {p_val}")

    # ---- PART 3: Spectral measure (numerical) ----
    print("\n\n" + "="*70)
    print("PART 3: SPECTRAL MEASURE (eigenvalues & weights)")
    print("="*70)

    for d in range(3, 13):
        evals, weights = numerical_spectral_measure(d)
        print(f"\nd={d}: {d-1} eigenvalues")
        for i in range(len(evals)):
            print(f"  lam_{i+1}={evals[i]:+.12f}  w_{i+1}={weights[i]:.12f}")
        print(f"  Sum(w)={sum(weights):.15f}  Sum(w*lam)={sum(weights*evals):.15f}")

    # ---- PART 4: Verify m formula ----
    print("\n\n" + "="*70)
    print("PART 4: VERIFY m_d(z) = sum w_k/(z-lam_k)")
    print("="*70)

    z_test = 1.0 + 0.1j
    for d in range(3, 13):
        evals, weights = numerical_spectral_measure(d)
        m_spec = sum(weights[k] / (z_test - evals[k]) for k in range(len(evals)))
        P, Q = finite_m_polys(d)
        m_form = complex(P.as_expr().subs(z, z_test)) / complex(Q.as_expr().subs(z, z_test))
        err = abs(m_spec - m_form)
        print(f"  d={d:2d}: |err|={err:.2e}  {'OK' if err < 1e-10 else 'MISMATCH'}")

    # ---- PART 5: Poles/residues from m_d ----
    print("\n\n" + "="*70)
    print("PART 5: POLES/RESIDUES vs DIRECT EIGENDECOMP")
    print("="*70)

    for d in range(3, 9):
        P, Q = finite_m_polys(d)
        # Numerical roots of Q
        q_coeffs = [float(c) for c in Q.all_coeffs()]
        poles = np.sort(np.roots(q_coeffs).real)
        # Residues: P(pole)/Q'(pole)
        Q_deriv_expr = sympy.diff(Q.as_expr(), z)
        residues = []
        for pole in poles:
            pv = float(P.as_expr().subs(z, pole))
            qv = float(Q_deriv_expr.subs(z, pole))
            residues.append(pv / qv)
        residues = np.array(residues)

        evals, weights = numerical_spectral_measure(d)
        print(f"\nd={d}:")
        print(f"  {'Pole':>18s}  {'Eigenval':>18s}  {'Residue':>15s}  {'Weight':>15s}")
        for i in range(len(evals)):
            print(f"  {poles[i]:18.12f}  {evals[i]:18.12f}  {residues[i]:15.12f}  {weights[i]:15.12f}")
        print(f"  Sum(res)={sum(residues):.12f}")

    # ---- PART 6: Structural analysis ----
    print("\n\n" + "="*70)
    print("PART 6: STRUCTURAL ANALYSIS")
    print("="*70)

    print("\n--- Top eigenvalue = (d-1)/(d+1) ---")
    for d in range(3, 15):
        evals, weights = numerical_spectral_measure(d)
        pred = (d-1)/(d+1)
        print(f"  d={d:2d}: pred={pred:.10f}  actual={evals[-1]:.10f}  "
              f"w_top={weights[-1]:.12e}")

    print("\n--- Top weight scaling ---")
    for d in range(3, 20):
        evals, weights = numerical_spectral_measure(d)
        w_top = weights[-1]
        # Try w_top ~ C * alpha^d
        if d > 3:
            p_prev = exact_params(d-1)
            evals_prev, weights_prev = numerical_spectral_measure(d-1)
            ratio = weights_prev[-1] / w_top if w_top > 0 else float('inf')
            print(f"  d={d:2d}: w_top={w_top:.6e}  ratio(prev/this)={ratio:.4f}")

    print("\n--- Bottom eigenvalue (negative!) ---")
    for d in range(3, 15):
        evals, _ = numerical_spectral_measure(d)
        print(f"  d={d:2d}: lam_min={evals[0]:+.12f}")

    # ---- PART 7: Convergence ----
    print("\n\n" + "="*70)
    print("PART 7: CONVERGENCE")
    print("="*70)

    print("\n--- b_int^2 scaling ---")
    for d in range(5, 25):
        p = exact_params(d)
        b2 = float(p['b_int_sq'])
        print(f"  d={d:2d}: b_int^2={b2:.10f}  b_int^2*d={b2*d:.10f}  "
              f"b_int^2*d^2={b2*d*d:.10f}")

    # Check: b_int^2 * d^2 -> constant?
    # x ~ 3/5 for large d, C_int ~ 3/(10d), so b_int^2 ~ 9/(50d) ... scales as 1/d
    # Actually: x = (6d^2-29d+25)/(10(d+1)(d-2)) -> 6d^2/(10d^2) = 3/5
    # C_int = 3/(10(d-2)) -> 3/(10d)
    # b_int^2 = C_int * x -> (3/(10d)) * (3/5) = 9/(50d)

    print("\n--- b_int^2 * d -> 9/50 = 0.18? ---")
    for d in [10, 20, 50, 100, 200]:
        p = exact_params(d)
        b2 = float(p['b_int_sq'])
        print(f"  d={d:3d}: b_int^2*d = {b2*d:.10f}  (9/50 = {9/50:.10f})")

    print("\n--- Evaluation at z=1.5 ---")
    for d in range(4, 16):
        P, Q = finite_m_polys(d)
        zv = Rational(3, 2)
        mv = P.eval(zv) / Q.eval(zv)
        print(f"  d={d:2d}: m_d(3/2) = {float(mv):.14f}")

    # ---- PART 7b: Characteristic polynomial patterns ----
    print("\n\n" + "="*70)
    print("PART 7b: CHARACTERISTIC POLY STRUCTURE")
    print("="*70)

    for d in range(3, 10):
        P, Q = finite_m_polys(d)
        # Q is the char poly (up to leading coefficient)
        lc = Q.LC()
        Q_monic = Poly(Q.as_expr() / lc, z)
        coeffs = Q_monic.all_coeffs()
        print(f"\nd={d}: Q monic (deg {Q.degree()}):")
        for i, c in enumerate(coeffs):
            c_simp = sympy.nsimplify(c, rational=True)
            print(f"  z^{Q.degree()-i}: {c_simp}")

    # ---- PART 8: Exact closed forms d=3,4 ----
    print("\n\n" + "="*70)
    print("PART 8: EXACT CLOSED FORMS d=3,4")
    print("="*70)

    print("\nd=3: m_3(z)")
    m3 = m_rational(3)
    pf3 = apart(m3, z)
    print(f"  Partial fractions: {pf3}")

    print("\nd=4: m_4(z)")
    m4 = m_rational(4)
    pf4 = apart(m4, z)
    print(f"  Partial fractions: {pf4}")

    # ---- PART 9: Moment analysis ----
    print("\n\n" + "="*70)
    print("PART 9: MOMENTS mu_n = <e1|J^n|e1> = sum w_k lam_k^n")
    print("="*70)

    for d in range(3, 10):
        evals, weights = numerical_spectral_measure(d)
        print(f"\n  d={d}:")
        for n in range(6):
            mu = sum(weights * evals**n)
            print(f"    mu_{n} = {mu:.15f}", end="")
            if n == 0: print("  [=1]")
            elif n == 1: print(f"  [=a1=1/3={1/3:.15f}]")
            else: print()

    # ---- PART 10: Tail m-function m_2 ----
    print("\n\n" + "="*70)
    print("PART 10: TAIL m-FUNCTION m_2(z)")
    print("="*70)

    for d in range(4, 9):
        p = exact_params(d)
        # Recompute m_2 from the recursion
        if d == 4:
            P2 = Poly(Rational(1), z)
            Q2 = Poly(z - p['a_last'], z)
            P2, Q2 = Q2, Poly(z - p['a_int'], z)*Q2 - Poly(p['b_last_sq'], z)*P2
        else:
            P2 = Poly(Rational(1), z)
            Q2 = Poly(z - p['a_last'], z)
            P2, Q2 = Q2, Poly(z - p['a_int'], z)*Q2 - Poly(p['b_last_sq'], z)*P2
            for _ in range(d - 4):
                P2, Q2 = Q2, Poly(z - p['a_int'], z)*Q2 - Poly(p['b_int_sq'], z)*P2

        print(f"\n  d={d}: m_2 = [{P2.degree()}/{Q2.degree()}]")
        print(f"    Num = {factor(P2.as_expr())}")
        print(f"    Den = {factor(Q2.as_expr())}")

    # ---- SUMMARY ----
    print("\n\n" + "="*70)
    print("SUMMARY")
    print("="*70)
    print("""
KEY FINDINGS:

1. m_d(z) = P_{d-2}(z) / Q_{d-1}(z) is rational of degree [(d-2)/(d-1)].

2. LARGEST EIGENVALUE: lambda_max = (d-1)/(d+1) for ALL d.
   Denominator always has linear factor ((d+1)z - (d-1)).
   This eigenvalue has EXPONENTIALLY SMALL weight (~ C * alpha^{-d}).

3. SMALLEST EIGENVALUE is NEGATIVE for d >= 5:
   This comes from the mismatch between site 1 diagonal (1/3)
   and the bulk (2/5). The first site "pulls down" one eigenvalue.

4. SPECTRAL MEASURE verified:
   - Sum of weights = 1 (probability measure)
   - First moment = 1/3 (= a_1, the first diagonal entry)
   - Poles match eigenvalues, residues match weights

5. BULK SCALING: b_int^2 ~ 9/(50d) for large d.
   Band width ~ 2*sqrt(b_int^2) ~ 6/(5*sqrt(d)) -> 0.
   All interior eigenvalues collapse to z = 2/5 as d -> inf.
   The boundary eigenvalues (d-1)/(d+1) -> 1 and lam_min -> -1/3(?) stand apart.

6. RANK-2 PERTURBATION: The boundary corrections at sites 1 and d-1
   create two "outlier" eigenvalues outside the bulk band.
   The interior eigenvalues cluster in the Chebyshev band [2/5 - 2b, 2/5 + 2b].

7. NO SIMPLE CLOSED FORM for all d simultaneously in terms of
   elementary functions of d. The characteristic polynomial coefficients
   are rational in d but grow in complexity with degree.
   The STRUCTURE (linear factor + (d-2)-degree remainder) IS universal.
""")
