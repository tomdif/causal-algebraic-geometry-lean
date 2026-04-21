"""
z3_rational_fit.py — Test whether |CC([m]^3)| admits a rational generating
function analogous to the 2D case Z_2(q,z) = D(q)^2 · (1-3z^2+z^3)/(1-z^2+z^3).

Note: the 2D "master formula" is a CONTINUUM PARTITION FUNCTION obtained by
resumming sectors labeled by (k,d) using the screening theorem
Theta_k(d,m) = (k+1)m + d(m-k), NOT the ordinary generating function
A(z) = sum_m |CC([m]^2)| z^m (which the paper notes is probably non-D-finite).

What we can test numerically:
 1. Does the ordinary generating function A_3(z) = sum_m |CC([m]^3)| z^m
    fit a rational function of small degree?
 2. Does log|CC([m]^3)|/m^2 admit the sandwich bounds' structure with a
    rational correction term?

Data (exact brute-force, April 19):
  m=1: 2
  m=2: 101
  m=3: 114,797
"""

import numpy as np
from fractions import Fraction


# Exact counts for convex subsets of [m]^d (brute force / verified).
# d=2: OEIS-style, verified transfer matrix
CC_2 = {
    1: 2, 2: 6, 3: 50, 4: 846, 5: 23094,
    6: 909033, 7: 48617852, 8: 3394282075,
}

# d=3: April 19 brute-force (post-TM-bug retraction)
CC_3 = {
    1: 2,
    2: 101,
    3: 114797,
}

# Known Q(m) values (full-support antitone pairs) from C3Conjecture docstring
Q = {
    1: 1,
    2: 20,
    3: 8790,
    4: 89613429,
    5: 21493411201893,
}


def test_rational_fit(values, max_denom_deg=4, max_numer_deg=4,
                      name="A(z)"):
    """Try to fit sum_m values[m] z^m to a rational function
       P(z)/Q(z) with deg P <= max_numer_deg, deg Q <= max_denom_deg.

    If sum_m a_m z^m = P(z)/Q(z) with Q(z) = 1 + q_1 z + ... + q_D z^D,
    then the sequence a_m satisfies the recurrence
       a_m + q_1 a_{m-1} + ... + q_D a_{m-D} = 0 for m > N = max_numer_deg.
    We need at least D + N + 1 values to detect such a recurrence.
    """
    vals = [values[k] for k in sorted(values.keys())]
    n_vals = len(vals)
    print(f"\n=== Testing rational fit for {name} ===")
    print(f"  {n_vals} exact values: {vals}")

    # Need enough values to detect the recurrence
    # For denom deg D, we need ~2D+1 values beyond the leading numerator
    for D in range(1, max_denom_deg + 1):
        for N in range(0, max_numer_deg + 1):
            # Recurrence applies for m > N; need D consecutive equations
            n_needed = N + D + D  # N initial + D eqs each using D prior
            if n_vals < n_needed:
                continue
            # Set up linear system for q_1, ..., q_D
            # For m = N+D, N+D+1, ..., n_vals-1:
            #   a_m = -sum_{j=1..D} q_j a_{m-j}
            # Use first D equations
            if n_vals - (N + D) < D:
                continue
            start = N + D
            rows = []
            rhs = []
            for m in range(start, min(start + D, n_vals)):
                rows.append([vals[m - j] for j in range(1, D + 1)])
                rhs.append(-vals[m])
            A = np.array(rows, dtype=object)
            b = np.array(rhs, dtype=object)
            # Solve via Fractions for exactness
            try:
                A_frac = [[Fraction(int(x)) for x in r] for r in rows]
                b_frac = [Fraction(int(x)) for x in rhs]
                q_sol = solve_frac(A_frac, b_frac)
                if q_sol is None:
                    continue
            except Exception:
                continue

            # Verify on remaining equations
            ok = True
            for m in range(start + D, n_vals):
                lhs = vals[m] + sum(q_sol[j - 1] * vals[m - j]
                                    for j in range(1, D + 1))
                if lhs != 0:
                    ok = False
                    break
            if ok:
                print(f"  FIT FOUND: deg(numer)<={N}, deg(denom)={D}")
                print(f"    Denominator coefs (1, q_1, ..., q_D) = (1, {q_sol})")
                # Compute numerator by multiplying a(z) by denom
                # P(z) = a(z) Q(z) up to z^N
                P = [Fraction(0)] * (N + 1)
                for i in range(N + 1):
                    P[i] = Fraction(vals[i] if i < n_vals else 0)
                    for j in range(1, min(D, i) + 1):
                        P[i] += q_sol[j - 1] * Fraction(vals[i - j])
                print(f"    Numerator coefs (p_0,...,p_N) = {P}")
                return (N, D, q_sol, P)
    print(f"  NO rational fit found up to (deg numer={max_numer_deg}, "
          f"deg denom={max_denom_deg})")
    return None


def solve_frac(A, b):
    """Gaussian elimination over Fractions. A is n x n list-of-lists."""
    n = len(A)
    if n == 0 or len(A[0]) != n:
        return None
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        # Pivot
        piv = None
        for r in range(col, n):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        # Normalize
        inv = Fraction(1) / M[col][col]
        M[col] = [x * inv for x in M[col]]
        # Eliminate
        for r in range(n):
            if r == col or M[r][col] == 0:
                continue
            fac = M[r][col]
            M[r] = [M[r][k] - fac * M[col][k] for k in range(n + 1)]
    return [M[i][n] for i in range(n)]


def fit_ln_Q(name="ln Q(m) / m^2"):
    """Numerical fit of log Q(m) / m^2 against hypothesized 2 L_3."""
    import math
    L3 = (9.0 / 2.0) * math.log(3.0) - 6.0 * math.log(2.0)
    print(f"\n=== {name} vs 2 L_3 = {2*L3:.6f} ===")
    for m, q in sorted(Q.items()):
        val = math.log(q) / (m * m) if m > 0 else 0.0
        print(f"  m={m}: ln Q / m^2 = {val:.6f}  (target 2 L_3 = {2*L3:.6f})")


def fit_ln_CC3():
    """log|CC([m]^3)|/m^2 for the values we have."""
    import math
    L3 = (9.0 / 2.0) * math.log(3.0) - 6.0 * math.log(2.0)
    print(f"\n=== log|CC([m]^3)|/m^2 at currently known m ===")
    print(f"  Sandwich: L_3 = {L3:.4f} <= c_3 <= 2 L_3 = {2*L3:.4f}")
    for m, c in sorted(CC_3.items()):
        val = math.log(c) / (m * m) if m > 0 else 0.0
        print(f"  m={m}: log|CC|/m^2 = {val:.4f}")


if __name__ == "__main__":
    # First test on d=2 data: confirm the ordinary generating function
    # A_2(z) = sum_m |CC([m]^2)| z^m is NOT D-finite / rational (paper claim).
    test_rational_fit(CC_2, max_denom_deg=3, max_numer_deg=3,
                       name="A_2(z) = sum |CC([m]^2)| z^m")

    # Test on d=3 data: we only have m=1,2,3, which is too few to detect any
    # rational fit of meaningful degree.
    test_rational_fit(CC_3, max_denom_deg=2, max_numer_deg=2,
                       name="A_3(z) = sum |CC([m]^3)| z^m")

    # Test the sandwich-side value log|CC|/m^2 at available m.
    fit_ln_CC3()

    # Lower bound Q(m): we have m=1..5, 5 values.
    test_rational_fit(Q, max_denom_deg=3, max_numer_deg=3,
                       name="Q(z) = sum Q(m) z^m")

    # Fit of ln Q to check trajectory to 2 L_3
    fit_ln_Q()

    # Key point: the 2D master formula Z = D(q)^2 * (1-3z^2+z^3)/(1-z^2+z^3)
    # is a CONTINUUM partition function built from the screening theorem
    # Theta_k(d,m) = (k+1)m + d(m-k). That theorem is 2D-specific: d=2 boundary
    # is a 1D profile, violations are points, screening is 1D-local.
    # For d=3 the boundary is a 2D surface; analogous screening would need
    # Theta_{K}({patch}, m) for 2D defect patches, which is a FUNCTION not a
    # small finite set of indices. The geometric-series resummation that gave
    # (1-z^2+z^3)^{-1} in 2D has no obvious 1D-closure-like analog in 3D.
    print()
    print("=== STRUCTURAL ANALYSIS ===")
    print("2D master formula Z_2(q,z) = D(q)^2 * R(z) with R rational:")
    print("  - q counts LOCAL HEIGHT fluctuations (universal D(q)^2 = 1/eta^2)")
    print("  - z = e^{-beta} counts DEPTH PENALTY via sectors (k, d)")
    print("  - Rational denom 1 - z^2 + z^3 comes from resumming a 1D chain")
    print("    of screened defects with threshold Theta_k(d,m) = (k+1)m+d(m-k)")
    print()
    print("For d=3, screening would need Theta_K(patch, m) where 'patch' is")
    print("a 2D subset of the boundary surface, not an index in a 1D walk.")
    print("The resummation that produced (1-z^2+z^3) in 2D has no direct")
    print("analog in 3D without further structural input.")
