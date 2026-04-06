"""
Chamber Polynomials P_n^(d)(x): Orthogonality measure via Stieltjes transform.

Jacobi matrix J_d is (d-1)x(d-1) tridiagonal with:
  Diagonal: {1/3, 2/5, ..., 2/5, 1/5}
  b_1^2 = 1/(5(d+1))
  b_int^2 = C_int * x_val   where C_int = 3/(10(d-2)), x_val defined below
  b_last^2 = ((d-1)/(d+1) - 1/5) * x_val
  Top eigenvalue: exactly (d-1)/(d+1)
"""

import numpy as np
from fractions import Fraction
from itertools import product as iprod
import sys

# ============================================================
# Part 0: Build the Jacobi matrix with exact rationals
# ============================================================

def build_jacobi_rational(d):
    """Build (d-1)x(d-1) Jacobi matrix with Fraction entries.
    Returns (diag, off_diag_sq) where off_diag_sq[k] = b_{k+1}^2 coupling k <-> k+1."""
    n = d - 1  # matrix size
    if n <= 0:
        return [], []

    # Diagonal entries
    diag = []
    if n == 1:
        # d=2: single entry -- but spec says first=1/3, last=1/5
        # For d=2, n=1, ambiguous. Use 1/3.
        diag = [Fraction(1, 3)]
        return diag, []

    diag.append(Fraction(1, 3))           # first
    for _ in range(n - 2):               # interior
        diag.append(Fraction(2, 5))
    diag.append(Fraction(1, 5))           # last

    # Couplings
    off_sq = []

    # b_1^2
    b1sq = Fraction(1, 5 * (d + 1))
    off_sq.append(b1sq)

    if n >= 3:
        # Interior couplings
        C_int = Fraction(3, 10 * (d - 2))
        x_val = Fraction(d - 1, d + 1) - Fraction(2, 5) - C_int
        for _ in range(n - 3):
            off_sq.append(C_int * x_val)

        # Last coupling
        b_last_sq = (Fraction(d - 1, d + 1) - Fraction(1, 5)) * x_val
        off_sq.append(b_last_sq)
    elif n == 2:
        # d=3: 2x2 matrix needs exactly 1 off-diagonal coupling = b1^2.
        # No interior or last coupling needed (already appended b1^2 above).
        pass

    return diag, off_sq


def jacobi_to_numpy(diag, off_sq):
    """Convert rational Jacobi data to numpy symmetric matrix."""
    n = len(diag)
    J = np.zeros((n, n))
    for i in range(n):
        J[i, i] = float(diag[i])
    for i in range(n - 1):
        b = float(off_sq[i]) ** 0.5 if float(off_sq[i]) >= 0 else 0.0
        J[i, i+1] = b
        J[i+1, i] = b
    return J


def jacobi_to_numpy_direct(diag, off_sq):
    """Build symmetric tridiagonal with J[i,i+1] = J[i+1,i] = sqrt(b_{i+1}^2)."""
    n = len(diag)
    J = np.zeros((n, n))
    for i in range(n):
        J[i, i] = float(diag[i])
    for i in range(n - 1):
        val = float(off_sq[i])
        if val < 0:
            print(f"  WARNING: b_{i+1}^2 = {off_sq[i]} = {val:.6e} < 0!")
            b = 0.0
        else:
            b = np.sqrt(val)
        J[i, i+1] = b
        J[i+1, i] = b
    return J


# ============================================================
# Part 1: Eigenvalues and weights for d=3,...,8
# ============================================================

def compute_spectrum(d):
    """Return eigenvalues and weights (first-component squared of eigenvectors)."""
    diag, off_sq = build_jacobi_rational(d)
    if len(diag) == 0:
        return np.array([]), np.array([]), diag, off_sq

    J = jacobi_to_numpy_direct(diag, off_sq)
    evals, evecs = np.linalg.eigh(J)

    # Weights = |v_k[0]|^2 (first component of each eigenvector, squared)
    weights = evecs[0, :] ** 2

    return evals, weights, diag, off_sq


print("=" * 80)
print("CHAMBER POLYNOMIALS: ORTHOGONALITY MEASURE")
print("=" * 80)

results = {}
for d in range(3, 9):
    print(f"\n{'='*60}")
    print(f"d = {d}   (matrix size {d-1}x{d-1})")
    print(f"{'='*60}")

    diag, off_sq = build_jacobi_rational(d)
    print(f"  Diagonal (rational): {[str(x) for x in diag]}")
    print(f"  b_k^2 (rational):    {[str(x) for x in off_sq]}")

    # Check for negative couplings
    for k, bsq in enumerate(off_sq):
        if bsq < 0:
            print(f"  ** b_{k+1}^2 = {bsq} is NEGATIVE -- matrix not real-symmetric!")

    evals, weights, _, _ = compute_spectrum(d)
    results[d] = (evals, weights)

    print(f"\n  Top eigenvalue target: {float(Fraction(d-1, d+1)):.10f}")
    if len(evals) > 0:
        print(f"  Top eigenvalue actual: {evals[-1]:.10f}")

    print(f"\n  {'k':>3}  {'eigenvalue':>18}  {'weight w_k':>18}  {'rational guess':>20}")
    print(f"  {'---':>3}  {'------------------':>18}  {'------------------':>18}  {'--------------------':>20}")

    for k in range(len(evals)):
        # Try to identify as simple rationals
        ev_frac = Fraction(evals[k]).limit_denominator(10000)
        wt_frac = Fraction(weights[k]).limit_denominator(10000)
        print(f"  {k:>3}  {evals[k]:>18.12f}  {weights[k]:>18.12f}  {str(ev_frac):>10} / {str(wt_frac):>10}")

    print(f"\n  Sum of weights: {weights.sum():.15f}  (should be 1)")
    print(f"  Sum of w_k * lam_k: {(weights * evals).sum():.15f}  (= mu_1 = a_1 = {float(diag[0]):.15f})")


# ============================================================
# Part 2: Pattern analysis of weights
# ============================================================

print("\n\n" + "=" * 80)
print("WEIGHT PATTERN ANALYSIS")
print("=" * 80)

for d in range(3, 9):
    evals, weights = results[d]
    n = d - 1
    print(f"\nd={d}: weights = {weights}")

    # Check if weights are related to binomial coefficients
    from math import comb
    binom_weights = np.array([comb(n-1, k) for k in range(n)], dtype=float)
    binom_weights /= binom_weights.sum()
    print(f"  Binomial (normalized): {binom_weights}")
    print(f"  Ratio w/binom: {weights / np.where(binom_weights > 0, binom_weights, 1)}")

    # Check SU(2) Clebsch-Gordan / Wigner pattern: w_k ~ (2k+1) for spin-j rep
    # For spin j = (n-1)/2, the weights in the z-basis are uniform...
    # More relevant: check w_k ~ sin^2(pi*(k+1)/(n+1)) (Chebyshev-like)
    cheb_weights = np.array([np.sin(np.pi * (k + 1) / (n + 1))**2 for k in range(n)])
    cheb_weights /= cheb_weights.sum()
    print(f"  Chebyshev sin^2: {cheb_weights}")
    print(f"  Ratio w/cheb:    {weights / np.where(cheb_weights > 0, cheb_weights, 1)}")


# ============================================================
# Part 3: Stieltjes transform and continued fraction
# ============================================================

print("\n\n" + "=" * 80)
print("STIELTJES TRANSFORM (from spectral decomposition)")
print("=" * 80)

def stieltjes_from_spectrum(z, evals, weights):
    """S(z) = sum_k w_k / (z - lam_k)"""
    return np.sum(weights / (z - evals))


def stieltjes_continued_fraction(z, diag, off_sq):
    """S(z) via continued fraction: 1/(z - a_1 - b_1^2/(z - a_2 - ...))"""
    n = len(diag)
    # Build from bottom up
    val = complex(z) - float(diag[n - 1])
    for k in range(n - 2, -1, -1):
        val = complex(z) - float(diag[k]) - float(off_sq[k]) / val
    return 1.0 / val


# Verify both methods agree
print("\nVerification: Spectral vs Continued Fraction at z = 1 + 0.1i")
for d in range(3, 9):
    evals, weights = results[d]
    diag, off_sq = build_jacobi_rational(d)
    z = 1.0 + 0.1j
    s_spec = stieltjes_from_spectrum(z, evals, weights)
    s_cf = stieltjes_continued_fraction(z, diag, off_sq)
    print(f"  d={d}: S_spec = {s_spec:.10f}, S_cf = {s_cf:.10f}, diff = {abs(s_spec - s_cf):.2e}")


# ============================================================
# Part 4: Closed form investigation
# ============================================================

print("\n\n" + "=" * 80)
print("CLOSED FORM INVESTIGATION")
print("=" * 80)

print("\nFor finite Jacobi matrices, S(z) = P_{n-1}(z) / P_n(z)")
print("where P_n is the characteristic polynomial of J_n.")
print("The measure is purely discrete (point masses at eigenvalues).")
print()

for d in range(3, 9):
    diag, off_sq = build_jacobi_rational(d)
    n = len(diag)

    # Build characteristic polynomial via recurrence:
    # P_0 = 1, P_1 = z - a_1, P_k = (z - a_k) P_{k-1} - b_{k-1}^2 P_{k-2}
    # We'll evaluate at several points and also build coefficients symbolically

    # Using numpy polynomial (coefficients in increasing power order)
    # P_k stored as list of Fraction coefficients [c_0, c_1, ..., c_k]
    def poly_mul_scalar(p, c):
        return [x * c for x in p]

    def poly_add(p, q):
        result = [Fraction(0)] * max(len(p), len(q))
        for i in range(len(p)):
            result[i] += p[i]
        for i in range(len(q)):
            result[i] += q[i]
        return result

    def poly_mul_z(p):
        """Multiply by z: shift coefficients up by 1."""
        return [Fraction(0)] + p

    def poly_sub(p, q):
        return poly_add(p, poly_mul_scalar(q, Fraction(-1)))

    # P_0 = 1
    P_prev2 = [Fraction(1)]
    # P_1 = z - a_1
    P_prev1 = [-diag[0], Fraction(1)]

    for k in range(1, n):
        # P_{k+1} = (z - a_{k+1}) P_k - b_k^2 P_{k-1}
        # (z - a_{k+1}) P_k = z*P_k - a_{k+1}*P_k
        term1 = poly_sub(poly_mul_z(P_prev1), poly_mul_scalar(P_prev1, diag[k]))
        term2 = poly_mul_scalar(P_prev2, off_sq[k-1])
        P_new = poly_sub(term1, term2)
        P_prev2 = P_prev1
        P_prev1 = P_new

    char_poly = P_prev1  # P_n(z) = characteristic polynomial
    numer_poly = P_prev2  # P_{n-1}(z) = numerator of S(z)

    print(f"d={d}: Characteristic polynomial P_{n}(z) coefficients (ascending powers):")
    for i, c in enumerate(char_poly):
        print(f"    z^{i}: {c}")

    # Verify: P_n should have roots at the eigenvalues
    evals, weights = results[d]
    print(f"  Eigenvalues: {evals}")

    # Check product of eigenvalues = (-1)^n * constant term / leading coeff
    prod_ev = 1
    for ev in evals:
        prod_ev *= ev
    det_check = float(char_poly[0]) * ((-1) ** n)
    print(f"  Product of eigenvalues: {prod_ev:.10f}")
    print(f"  (-1)^n * P_n(0):       {det_check:.10f}")

    # Weights from residues: w_k = P_{n-1}(lam_k) / P_n'(lam_k)
    # (alternative to eigenvector method)
    print()


# ============================================================
# Part 5: Moment sequence
# ============================================================

print("\n" + "=" * 80)
print("MOMENT SEQUENCE: mu_n = integral x^n d mu = sum_k w_k * lam_k^n")
print("=" * 80)

for d in range(3, 9):
    evals, weights = results[d]
    print(f"\nd={d}:")
    moments = []
    for n in range(11):
        mu_n = np.sum(weights * evals**n)
        moments.append(mu_n)
        # Try rational approximation
        mu_frac = Fraction(mu_n).limit_denominator(100000)
        print(f"  mu_{n:>2} = {mu_n:>20.14f}   approx {mu_frac}")

    # Check: Hankel determinants (should be > 0 for a valid measure)
    print(f"  Hankel det check:")
    for size in range(1, min(len(evals) + 1, 5)):
        H = np.array([[moments[i+j] for j in range(size)] for i in range(size)])
        det_H = np.linalg.det(H)
        print(f"    H_{size} det = {det_H:.10e}  {'> 0' if det_H > 0 else '<= 0 WARNING'}")


# ============================================================
# Part 6: Cross-dimensional patterns
# ============================================================

print("\n\n" + "=" * 80)
print("CROSS-DIMENSIONAL PATTERNS")
print("=" * 80)

print("\nTop eigenvalue (should be (d-1)/(d+1)):")
for d in range(3, 9):
    evals, weights = results[d]
    target = (d - 1) / (d + 1)
    print(f"  d={d}: lambda_max = {evals[-1]:.12f}, target = {target:.12f}, diff = {evals[-1] - target:.2e}")

print("\nWeight of top eigenvalue:")
for d in range(3, 9):
    evals, weights = results[d]
    w_top = weights[-1]
    frac = Fraction(w_top).limit_denominator(10000)
    print(f"  d={d}: w_top = {w_top:.12f}, approx = {frac}, 1/d = {1/d:.12f}, 1/(d+1) = {1/(d+1):.12f}")

print("\nWeight of smallest eigenvalue:")
for d in range(3, 9):
    evals, weights = results[d]
    w_bot = weights[0]
    frac = Fraction(w_bot).limit_denominator(10000)
    print(f"  d={d}: w_bot = {w_bot:.12f}, approx = {frac}")

print("\nSmallest eigenvalue:")
for d in range(3, 9):
    evals, weights = results[d]
    frac = Fraction(evals[0]).limit_denominator(10000)
    print(f"  d={d}: lambda_min = {evals[0]:.12f}, approx = {frac}")

print("\nMean of measure (mu_1 = sum w_k lam_k, should = a_1 = 1/3):")
for d in range(3, 9):
    evals, weights = results[d]
    mu1 = np.sum(weights * evals)
    print(f"  d={d}: mu_1 = {mu1:.15f}")

print("\nVariance of measure (mu_2 - mu_1^2):")
for d in range(3, 9):
    evals, weights = results[d]
    mu1 = np.sum(weights * evals)
    mu2 = np.sum(weights * evals**2)
    var = mu2 - mu1**2
    frac = Fraction(var).limit_denominator(100000)
    print(f"  d={d}: var = {var:.15f}, approx = {frac}")


# ============================================================
# Part 7: Weight ratios and combinatorial patterns
# ============================================================

print("\n\n" + "=" * 80)
print("WEIGHT RATIOS (consecutive)")
print("=" * 80)

for d in range(3, 9):
    evals, weights = results[d]
    n = len(weights)
    print(f"\nd={d}:")
    for k in range(n - 1):
        ratio = weights[k+1] / weights[k] if weights[k] > 1e-15 else float('inf')
        frac = Fraction(ratio).limit_denominator(10000)
        print(f"  w_{k+1}/w_{k} = {ratio:.10f}  approx {frac}")

print("\n\n" + "=" * 80)
print("EIGENVALUE SPACING RATIOS")
print("=" * 80)

for d in range(3, 9):
    evals, _ = results[d]
    n = len(evals)
    if n >= 3:
        print(f"\nd={d}:")
        spacings = np.diff(evals)
        for k in range(len(spacings) - 1):
            ratio = spacings[k+1] / spacings[k] if abs(spacings[k]) > 1e-15 else float('inf')
            print(f"  gap_{k+1}/gap_{k} = {ratio:.10f}")


# ============================================================
# Part 8: Check d=3 analytically
# ============================================================

print("\n\n" + "=" * 80)
print("ANALYTIC CHECK: d=3 (2x2 matrix)")
print("=" * 80)

d = 3
a1 = Fraction(1, 3)
a2 = Fraction(1, 5)
b1sq = Fraction(1, 5 * (d + 1))  # 1/20

print(f"J_3 = [[{a1}, sqrt({b1sq})], [sqrt({b1sq}), {a2}]]")
print(f"a1 = {a1}, a2 = {a2}, b1^2 = {b1sq}")

# For d=3, there may also be a b_last coupling
diag3, off3 = build_jacobi_rational(3)
print(f"Full diagonal: {diag3}")
print(f"Full couplings: {off3}")

trace = a1 + a2
det_val = a1 * a2 - b1sq
disc = trace**2 - 4 * det_val

print(f"\nTrace = {trace}")
print(f"Det = {det_val}")
print(f"Discriminant = {disc}")

# eigenvalues = (trace +/- sqrt(disc)) / 2
import sympy
disc_s = sympy.Rational(int(disc.numerator), int(disc.denominator))
trace_s = sympy.Rational(int(trace.numerator), int(trace.denominator))
sqrt_disc = sympy.sqrt(disc_s)

lam1 = (trace_s - sqrt_disc) / 2
lam2 = (trace_s + sqrt_disc) / 2
print(f"\nlam_1 = ({trace_s} - sqrt({disc_s})) / 2 = {lam1} = {float(lam1):.12f}")
print(f"lam_2 = ({trace_s} + sqrt({disc_s})) / 2 = {lam2} = {float(lam2):.12f}")
print(f"Target top = {Fraction(d-1,d+1)} = {float(Fraction(d-1,d+1)):.12f}")

# Eigenvectors: (a1-lam, b) rotated
# For eigenvector v = (v1, v2), (J - lam I)v = 0
# (a1 - lam) v1 + b v2 = 0 => v2/v1 = -(a1 - lam)/b
# Weight = v1^2 / (v1^2 + v2^2)

b1 = sympy.sqrt(sympy.Rational(int(b1sq.numerator), int(b1sq.denominator)))

for lam, name in [(lam1, "lam_1"), (lam2, "lam_2")]:
    ratio = -(sympy.Rational(int(a1.numerator), int(a1.denominator)) - lam) / b1
    w = 1 / (1 + ratio**2)
    print(f"\n  {name}: v2/v1 = {ratio}, w = 1/(1+r^2) = {sympy.simplify(w)} = {float(w):.12f}")


# ============================================================
# Part 9: KEY DISCOVERIES SUMMARY
# ============================================================

print("\n\n" + "=" * 80)
print("KEY DISCOVERIES")
print("=" * 80)

print("\n1. VARIANCE = b_1^2 = 1/(5(d+1))  [EXACT]")
print("   This is a universal identity for Jacobi matrices: Var(mu) = b_1^2.")
print("   Proof: mu_2 = a_1^2 + b_1^2 (from recurrence), so Var = mu_2 - mu_1^2 = b_1^2.")
for d in range(3, 9):
    evals, weights = results[d]
    mu1 = np.sum(weights * evals)
    mu2 = np.sum(weights * evals**2)
    var = mu2 - mu1**2
    target = 1 / (5 * (d + 1))
    print(f"   d={d}: Var = {var:.15f}, 1/(5(d+1)) = {target:.15f}, diff = {abs(var-target):.2e}")

print("\n2. TOP EIGENVALUE = (d-1)/(d+1)  [EXACT by construction]")

print("\n3. TOP WEIGHT DECAY (exponential in d):")
for d in range(3, 9):
    evals, weights = results[d]
    w_top = weights[-1]
    if d > 3:
        prev_w = results[d-1][1][-1]
        ratio = w_top / prev_w
        print(f"   d={d}: w_top = {w_top:.10e}, ratio to d-1: {ratio:.6f}")
    else:
        print(f"   d={d}: w_top = {w_top:.10e}")

print("\n4. BOTTOM WEIGHT DECAY (even faster):")
for d in range(3, 9):
    evals, weights = results[d]
    w_bot = weights[0]
    if d > 3:
        prev_w = results[d-1][1][0]
        ratio = w_bot / prev_w
        print(f"   d={d}: w_bot = {w_bot:.10e}, ratio to d-1: {ratio:.6f}")
    else:
        print(f"   d={d}: w_bot = {w_bot:.10e}")

print("\n5. MEASURE CONCENTRATES: as d -> infty, measure concentrates")
print("   Support spreads (lambda_min decreases), but weight concentrates on interior.")
for d in range(3, 9):
    evals, weights = results[d]
    # Effective number of support points (participation ratio)
    PR = 1.0 / np.sum(weights**2)
    print(f"   d={d}: n={d-1} points, participation ratio = {PR:.4f}")

print("\n6. MOMENT mu_2 PATTERN:")
for d in range(3, 9):
    evals, weights = results[d]
    mu2 = np.sum(weights * evals**2)
    # mu_2 = a_1^2 + b_1^2 = 1/9 + 1/(5(d+1))
    target = Fraction(1, 9) + Fraction(1, 5 * (d + 1))
    print(f"   d={d}: mu_2 = {mu2:.15f}, 1/9 + 1/(5(d+1)) = {float(target):.15f}, match = {abs(mu2 - float(target)) < 1e-12}")

print("\n7. MOMENT mu_3 PATTERN:")
print("   From Jacobi theory: mu_3 = a_1^3 + 2*a_1*b_1^2 + a_2*b_1^2")
print("                     = a_1*(a_1^2 + b_1^2) + a_2*b_1^2 = a_1*mu_2 + a_2*b_1^2")
for d in range(3, 9):
    evals, weights = results[d]
    diag, off_sq = build_jacobi_rational(d)
    mu3 = np.sum(weights * evals**3)
    a1 = float(diag[0])
    a2 = float(diag[1])
    b1sq = float(off_sq[0])
    mu2 = np.sum(weights * evals**2)
    target = a1**3 + 2*a1*b1sq + a2*b1sq
    print(f"   d={d}: mu_3 = {mu3:.15f}, target = {target:.15f}, match = {abs(mu3 - target) < 1e-12}")

print("\n8. d=3 EXACT (sympy):")
print("   lambda_1 = 1/30, lambda_2 = 1/2")
print("   w_1 = 5/14, w_2 = 9/14")
print("   mu = (5/14)*delta(x - 1/30) + (9/14)*delta(x - 1/2)")

print("\n9. d=4 EXACT: w_top = 1/3 [EXACT]")
evals4, weights4 = results[4]
print(f"   w_top = {weights4[-1]:.15f}")
print(f"   Residue formula: w_top = P_2(3/5) / P_3'(3/5)")

print("\n\n" + "=" * 80)
print("DONE")
print("=" * 80)
