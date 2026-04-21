"""
z3_sector_expansion.py — Test whether the 2D sector resummation
(yielding R(z) = (1-3z^2+z^3)/(1-z^2+z^3)) has a natural 3D analog.

The 2D formula comes from this chain of reasoning:

  1. Envelope slope law: slope(S) = d_max + gap_blocks + 2 (19 cases)
  2. Universal spectrum: D(q)^2 = 1/eta(q)^2 = A000712 (local fluctuations)
  3. Screening theorem: Theta_k(d, m) = (k+1) m + d (m-k)
  4. Sector sum:
       Z_m(q) = Z_free(q)*[1 + sum_{k>=1} (-1)^k 2 sum_d C(k,d) q^{Theta_k(d,m)}]
  5. In the scaling limit z = q^m fixed (or z = e^{-beta}), the sum resums:
       Z_CC / Z_free -> R(z) = (1 - 3 z^2 + z^3) / (1 - z^2 + z^3)

Key observation: in 2D, the sector index (k, d) is two INTEGERS and the
threshold Theta_k(d,m) is LINEAR in both. That makes the sum a geometric
series, giving a rational R(z).

For d=3, the analog would replace (k, d) with a more complex defect label.
Specifically:
  - A violation in 2D is a single position (a point in [m]).
  - A violation in 3D is a 2D boundary patch (potentially a shape in [m]^2).

Let's test whether any small rational form for d=3 is consistent with what
we DO have: the sandwich numbers and the Q(m) lower bound.
"""

import numpy as np
from fractions import Fraction
import math


def eval_R_2d(z):
    """2D master formula: R(z) = (1 - 3 z^2 + z^3) / (1 - z^2 + z^3)."""
    return (1 - 3*z*z + z*z*z) / (1 - z*z + z*z*z)


def series_R_2d(n_terms=20):
    """Power series of R(z)."""
    # R(z) = N(z)/D(z). Compute via long division.
    N = [1, 0, -3, 1] + [0]*(n_terms - 3)  # 1 - 3z^2 + z^3
    D = [1, 0, -1, 1] + [0]*(n_terms - 3)   # 1 - z^2 + z^3
    a = [0]*n_terms
    for i in range(n_terms):
        val = N[i] if i < len(N) else 0
        for j in range(1, min(i, len(D)) + 1):
            val -= D[j] * a[i-j]
        a[i] = val / D[0]
    return a


def scan_rational_forms_for_d3():
    """Scan small rational forms that could serve as a 3D analog of R(z).

    The 2D denominator is 1 - z^2 + z^3. Natural guesses:
       (a) 1 - z^3 + z^4 (bump each degree by 1)
       (b) (1 - z^2 + z^3)^2 (square the 2D denominator — layered sectors)
       (c) 1 - a z^2 + b z^3 + c z^4 + d z^5 + ...
    """
    print("\n=== Candidate 3D rational forms ===")
    print()
    print("Formal candidates inspired by the 2D denominator 1 - z^2 + z^3:")
    print()

    candidates = [
        ("(1-z^3+z^4)", [1, 0, 0, -1, 1]),
        ("(1-z^2+z^3)^2", conv([1,0,-1,1], [1,0,-1,1])),
        ("(1-z^3+z^5)", [1, 0, 0, -1, 0, 1]),
        ("(1-2z^2+z^3)", [1, 0, -2, 1]),
        ("(1-z+z^3)", [1, -1, 0, 1]),
    ]
    for name, d in candidates:
        # Find nearest real root
        poly = np.array(d)
        roots = np.roots(poly[::-1])  # numpy wants highest-degree first
        real_roots = [r.real for r in roots if abs(r.imag) < 1e-10]
        nearest = min(real_roots, key=abs) if real_roots else None
        zc = nearest
        rate = abs(1.0/zc) if zc is not None else None
        print(f"  {name:25s}  nearest real root ~ {zc}  "
              f"growth 1/|z_c| ~ {rate}")


def conv(a, b):
    """Polynomial convolution."""
    n = len(a) + len(b) - 1
    c = [0] * n
    for i in range(len(a)):
        for j in range(len(b)):
            c[i+j] += a[i] * b[j]
    return c


def check_sandwich_consistency():
    """Check whether the d=3 sandwich values are consistent with
    a CONTINUUM formula Z_3 = D(q)^? * R_3(z) with rational R_3."""
    import math
    L3 = (9.0/2.0)*math.log(3.0) - 6.0*math.log(2.0)
    CC_3 = {1: 2, 2: 101, 3: 114797}
    print()
    print("=== Sandwich consistency for d=3 ===")
    print(f"  L_3 = {L3:.4f}, 2*L_3 = {2*L3:.4f}")
    for m, c in sorted(CC_3.items()):
        lncc = math.log(c) / (m*m)
        print(f"  m={m}: log|CC|/m^2 = {lncc:.4f}  "
              f"(ratio to 2 L_3 = {lncc/(2*L3):.3f})")
    # Trajectory: 0.693, 1.154, 1.295 — still climbing, consistent
    # with sandwich [L_3, 2*L_3] = [0.785, 1.570] but not yet
    # resolving which end it approaches.


def test_ratio_to_Zfree():
    """In 2D, R(z) = Z_CC / Z_free is a clean rational function.
    Can we define a meaningful Z_free for d=3?

    Z_free for d=2 = sum over antitone pairs (D, U) from [m] -> [m+1]
    WITHOUT the convexity constraint D > U pointwise. This gives
    C(2m, m)^2 ~ 16^m.

    For d=3: Z_free = (#antitone functions [m]^2 -> [m+1])^2
    But the convexity constraint is different (it's not just "pairs").
    In d=3 we have downsets of [m]^3 with two layers of antitone data,
    which does NOT reduce to a pair of d=2 antitone functions in the
    same simple way.
    """
    import math
    # d=2: Z_free(m) = binom(2m,m)^2, Z_CC(m) = |CC([m]^2)|
    from math import comb
    print()
    print("=== 2D: Z_CC / Z_free ratio (should -> R(1) = -1? No: R(1)=-1) ===")
    print("    R(1) = (1-3+1)/(1-1+1) = -1/1 = -1 — but this is the ALGEBRAIC")
    print("    value at z=1, not a physical limit. The physical ratio is at")
    print("    the relevant scaling of z vs m. See memory file for details.")
    CC_2 = {1: 2, 2: 6, 3: 50, 4: 846, 5: 23094, 6: 909033, 7: 48617852}
    for m, c in sorted(CC_2.items()):
        zfree = comb(2*m, m)**2
        print(f"  m={m}: |CC|={c}  Z_free={zfree}  "
              f"ratio={c/zfree:.6f}  log ratio/m={math.log(c/zfree)/m:.4f}")


if __name__ == "__main__":
    print("2D master formula R(z) = (1 - 3 z^2 + z^3) / (1 - z^2 + z^3)")
    print("Power series expansion (first 15 terms):")
    a = series_R_2d(15)
    print(f"  {[f'{x:.4g}' for x in a]}")
    print(f"  R(0) = {a[0]}, R(0.5) = {eval_R_2d(0.5):.4f}")
    print(f"  Growth rate of coefficients (should be ~ 1.3247):")
    for i in range(5, 14):
        if abs(a[i]) > 1e-10 and abs(a[i+1]) > 1e-10:
            print(f"    a[{i+1}]/a[{i}] = {a[i+1]/a[i]:.4f}")

    scan_rational_forms_for_d3()
    check_sandwich_consistency()
    test_ratio_to_Zfree()

    print()
    print("=== BOTTOM LINE ===")
    print("The 2D R(z) is not the ordinary generating function of |CC|.")
    print("It is a CONTINUUM partition function ratio obtained via resumming")
    print("sectors (k,d) indexed by the screening theorem.")
    print()
    print("For d=3 there is NO analogous screening theorem available in the")
    print("project. Defects on a 2D boundary surface don't reduce to a 1D")
    print("chain of points. The sector sum that resummed to a degree-3")
    print("denominator in 2D has no natural 3D analog.")
    print()
    print("Numerical data (m=1,2,3 with only 3 values) is radically")
    print("insufficient to fit any rational structure — 3 data points can")
    print("match any 3-parameter rational, meaninglessly.")
