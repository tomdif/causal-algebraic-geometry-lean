"""
Berman-Koehler polynomial formulas for |J(2*2*m*n)|.

Strategy: |J(2*2*m*n)| is a polynomial in n of degree 4m. We compute
the values |J(2*2*m*n)| for n = 0,1,...,4m by direct enumeration using
Corollary 3.2 iterated, then interpolate.

Corollary 3.2: |S(X x [n])| = sum_{I in S(X)} |S(I x [n-1])|

Iterating: let Y = 2*2*m (a 3D poset). Then
  |S(Y x [n])| = sum_{I in S(Y)} |S(I x [n-1])|

And |S(I x [n-1])| for an order ideal I of Y (which is a 3D shape) is
computable: by induction, with one more iteration of Corollary 3.2 we
reduce to counting order ideals of 2D subposets. But that's again a
recursion that only terminates when we get to 2D shapes where MacMahon
applies (Theorem 3.3).

Simpler approach: since |J(P x [n])| is polynomial in n of known degree
(= |P|), just interpolate. We compute |J(2*2*m*[n])| for n = 0..4m by
direct enumeration of order ideals of 2*2*m*n (using Chains as "2x2xm"
poset and running the Corollary 3.2 recursion ONCE to express as a sum
over order ideals of 2*2*m of counts of order ideals of sub-shapes x [n-1]).

Even simpler: just directly count order ideals of the 4D poset 2*2*m*n
for small (m, n). Polynomial in n once m fixed.

An order ideal of 2*2*m*n is an antichain-labeling
f: [2]x[2]x[m] -> {0,1,...,n} that is order-reversing, i.e.
f(i,j,k) >= f(i',j',k') whenever i<=i', j<=j', k<=k'.

Equivalently, it is a plane-partition-like stack: for each (i,j,k) in [2]x[2]x[m]
(with 0-indexing), a height h(i,j,k) in {0,...,n}, with the monotone condition.

Number of such functions = |J(2*2*m*n)| where we use the convention that
2 = chain of length 2 = 2 elements, so [2] x [2] x [m] x [n] has 2*2*m*n
elements.

Let's be careful about conventions. In Berman-Koehler, "k" in their underline
notation is a chain with k elements. So "2 x 2 x 2 x n" = a 4D product where
the last factor is a chain of n elements.

|J(P)| = # order ideals of P = # antichains = # monotone 0/1 labelings.
For a product of chains, |J(a*b*c*d)| = # (a,b,c)-shape plane partitions with
parts at most d-1, equivalently # (a,b,c)-shape plane partitions with parts
at most d (if using parts in {0,...,d}), but depends on convention.

Most importantly: the empirical G.F. for A056360 tells us what we need:
  A056360 = |J(2*2*3*n)| with:
  G.F. = (1 + 36x + 279x^2 + 594x^3 + 279x^4 + 36x^5 + x^6)*(1+x) / (1-x)^13
        wait the user says (x+1)(x^6+36x^5+279x^4+594x^3+279x^2+36x+1)/(1-x)^13
  First few terms: A(0), A(1), ...
"""

import sys
from functools import lru_cache
from itertools import product
from fractions import Fraction

sys.setrecursionlimit(100000)


def count_order_ideals_product_chains(shape):
    """
    Count order ideals of the product poset [a_1] x ... x [a_k] where
    [a] is a chain with a elements (0, 1, ..., a-1), partial order
    coordinate-wise.

    An order ideal is specified by a monotone 0/1 function on the product:
    chi(p) = 1 and p' <= p implies chi(p') = 1.

    Equivalently, the "upper boundary" is an antichain. We'll use the
    direct algorithm: an order ideal of a product of chains shape
    (a_1,...,a_k) is a plane-partition-like stack with "heights"
    h(i_1,...,i_{k-1}) in {0,...,a_k} for each (i_1,...,i_{k-1}) in
    [a_1]x...x[a_{k-1}], monotone decreasing.

    For k=1: |J([a])| = a+1.

    We recursively peel off one dimension. We transfer: an order ideal of
    [a_1] x ... x [a_k] is equivalent to a k-tuple of order ideals of
    [a_1]x...x[a_{k-1}] forming a chain in the ideal lattice, of length
    a_k+1, i.e., I_0 ⊇ I_1 ⊇ ... ⊇ I_{a_k-1} (using slices at each level
    of the last coordinate).

    Equivalently, an order ideal of shape x [n] (last chain has n elements)
    corresponds to a weakly-decreasing sequence of n order ideals of shape.

    Wait - let's be very careful. We want "monotone 0/1 on [a_1]x...x[a_k]"
    where chi is monotone DOWN (ideal contains everything below a member).
    Slicing at last coordinate i_k = j gives I_j = {p' : chi(p', j)=1},
    an order ideal of [a_1]x...x[a_{k-1}]. Monotonicity says
    (p', j-1) <= (p', j), so chi(p', j-1) >= chi(p', j), hence I_0 ⊇ I_1 ⊇ ... ⊇ I_{a_k-1}.

    So |J(shape x [n])| = # weakly-decreasing chains of length n of order
    ideals of shape.
    """
    if len(shape) == 0:
        return 1
    if len(shape) == 1:
        return shape[0] + 1

    # Get all order ideals of shape[:-1]
    ideals = list_order_ideals_product(shape[:-1])
    # Order ideals of full shape = weakly-decreasing chains of length shape[-1]
    # in the ideal lattice (which is itself a distributive lattice with order
    # given by inclusion).
    #
    # # of such chains = coefficient in transfer matrix.

    # Count by transfer matrix: f[I] = number of chains ending at I.
    # Start with f_0[I] = 1 for all I. Then for each level:
    # f_{t+1}[I] = sum_{J >= I} f_t[J] (J contains I, i.e., J \supseteq I).
    # Result = sum_I f_{shape[-1]}[I].
    n = shape[-1]
    if n == 0:
        return 1  # Empty product poset has one (empty) order ideal.
    ideals_fs = [frozenset(I) for I in ideals]
    # Compute containment structure: for each I, list the J with J ⊇ I.
    parents = {I: [J for J in ideals_fs if I.issubset(J)] for I in ideals_fs}

    # f_t[I] = # chains of ideals of length t+1 ending at I (i.e., I_0 ⊇ ... ⊇ I_t = I).
    # Start: f_0[I] = 1 for all I.
    # Transition: f_{t+1}[I] = sum_{J ⊇ I} f_t[J].
    # We want # chains of length n = sum_I f_{n-1}[I], so iterate n-1 times.
    f = {I: 1 for I in ideals_fs}
    for _ in range(n - 1):
        new_f = {}
        for I in ideals_fs:
            new_f[I] = sum(f[J] for J in parents[I])
        f = new_f
    return sum(f.values())


def list_order_ideals_product(shape):
    """
    List all order ideals of the product of chains with given shape as
    tuples of points. Each point is a tuple of coordinates in
    [a_1] x ... x [a_k].
    """
    if len(shape) == 0:
        return [()]  # single empty ideal (empty poset has one ideal = the empty set)

    if len(shape) == 1:
        # Ideals of chain [a_1] are {0,...,j-1} for j in 0..a_1.
        a = shape[0]
        if a == 0:
            return [()]
        return [tuple((i,) for i in range(j)) for j in range(a + 1)]

    # General case: ideals of shape x [a_k] = chains of ideals of shape
    # of length a_k.
    if shape[-1] == 0:
        return [()]
    sub_ideals = list_order_ideals_product(shape[:-1])
    sub_ideal_sets = [frozenset(I) for I in sub_ideals]
    # Build containment graph: I -> list of J with J ⊆ I.
    subsets = {I: [J for J in sub_ideal_sets if J.issubset(I)] for I in sub_ideal_sets}

    a = shape[-1]
    # Enumerate weakly-decreasing chains I_0 ⊇ I_1 ⊇ ... ⊇ I_{a-1}.
    all_ideals = []

    def extend(prefix, k):
        # prefix = list of ideals so far (length k), I_0, ..., I_{k-1}.
        if k == a:
            # Build the 4D (k-dim) order ideal
            points = []
            for level, I in enumerate(prefix):
                for p in I:
                    points.append(p + (level,))
            all_ideals.append(tuple(sorted(points)))
            return
        if k == 0:
            for I in sub_ideal_sets:
                extend([I], 1)
        else:
            last = prefix[-1]
            for I in subsets[last]:
                extend(prefix + [I], k + 1)

    extend([], 0)
    return all_ideals


def count_J(shape):
    """|J(shape)| = number of order ideals of product of chains with given shape."""
    return count_order_ideals_product_chains(shape)


def interpolate_polynomial(values):
    """
    Given values[0], values[1], ..., values[d], return polynomial p(n)
    of degree <= d such that p(k) = values[k] for k = 0,...,d.
    Uses Lagrange interpolation with exact rational arithmetic and returns
    the polynomial as a list of coefficients [c_0, c_1, ..., c_d] where
    p(n) = sum c_i * n^i.
    """
    d = len(values) - 1
    # Build polynomial directly by Lagrange: p(n) = sum values[i] * L_i(n)
    # where L_i(n) = prod_{j != i} (n-j)/(i-j).
    coeffs = [Fraction(0)] * (d + 1)
    for i, vi in enumerate(values):
        # L_i(n) = prod_{j != i} (n - j) / (i - j)
        num = [Fraction(1)]  # polynomial 1
        denom = Fraction(1)
        for j in range(d + 1):
            if j == i:
                continue
            # multiply num by (n - j)
            new_num = [Fraction(0)] * (len(num) + 1)
            for k, c in enumerate(num):
                new_num[k] -= c * j
                new_num[k + 1] += c
            num = new_num
            denom *= (i - j)
        factor = Fraction(vi) / denom
        for k, c in enumerate(num):
            coeffs[k] += factor * c
    return coeffs


def binomial(n, k):
    from math import comb
    return comb(n, k)


def polynomial_in_binomial_basis(coeffs_monomial, max_degree):
    """
    Given a polynomial p(n) in the monomial basis (coeffs_monomial = [c_0,...,c_d]
    with p(n) = sum c_i n^i), re-express it in the basis C(n+k, k) for k=0,...,max_degree.
    Specifically: p(n) = sum_k b_k * C(n+k, k), return b_k.

    C(n+k, k) is a polynomial of degree k in n with leading coefficient 1/k!.
    Use Gaussian reduction by matching leading coefficients.
    """
    # Convert coeffs_monomial to a list of Fractions.
    c = [Fraction(v) for v in coeffs_monomial]
    # Pad up to max_degree.
    while len(c) < max_degree + 1:
        c.append(Fraction(0))
    # Represent C(n+k, k) as monomial coefficients.
    binom_polys = []
    for k in range(max_degree + 1):
        # C(n+k, k) = (n+k)(n+k-1)...(n+1) / k!
        poly = [Fraction(1)]
        for j in range(1, k + 1):
            # multiply by (n + j)
            new_poly = [Fraction(0)] * (len(poly) + 1)
            for m, coef in enumerate(poly):
                new_poly[m] += coef * j
                new_poly[m + 1] += coef
            poly = new_poly
        # divide by k!
        from math import factorial
        poly = [v / factorial(k) for v in poly]
        binom_polys.append(poly)
    # Solve: find b_k such that sum b_k * binom_polys[k] = c.
    # Go from top degree down.
    b = [Fraction(0)] * (max_degree + 1)
    remaining = c[:]
    for k in range(max_degree, -1, -1):
        # Leading coefficient of binom_polys[k] in n^k is 1/k!.
        from math import factorial
        lead = Fraction(1) / factorial(k)
        # We need remaining[k] = b_k * lead.
        b_k = remaining[k] / lead
        b[k] = b_k
        # Subtract b_k * binom_polys[k] from remaining.
        for m, coef in enumerate(binom_polys[k]):
            remaining[m] -= b_k * coef
    return b


def run_222_check():
    """Verify we reproduce Berman-Koehler's |J(2*2*2*n)| polynomial."""
    print("=" * 70)
    print("Reproducing Berman-Koehler: |J(2*2*2*n)|")
    print("=" * 70)
    # Degree is 2*2*2 = 8, so need 9 values.
    # Compute |J(2*2*2*n)| for n = 0, 1, ..., 9.
    values = []
    for n in range(10):
        v = count_J((2, 2, 2, n))
        # Note: n=0 means the last chain has 0 elements, i.e. empty poset factor.
        # Actually [0] has 0 elements so [2]x[2]x[2]x[0] = empty product...
        # In Berman-Koehler's convention, "n" is a chain with n elements, so n=0
        # means empty factor, and |J(2*2*2*0)| = |J(emptyset)| = 1.
        # But the 9-point polynomial fit requires n=0 in terms of "n such that
        # last chain has n elements plus maybe offset".
        # To match their formula, let's compute for what THEY mean by n.
        # Their formula: 48*C(n+8,8) - 96*C(n+7,7) + 63*C(n+6,6) - 15*C(n+5,5) + C(n+4,4)
        # At n = 0: 48*C(8,8) - 96*C(7,7) + 63*C(6,6) - 15*C(5,5) + C(4,4)
        #         = 48 - 96 + 63 - 15 + 1 = 1.  Good, |J(2*2*2*0)| = 1.
        # So their n is the size of the last chain.
        values.append(v)
        print(f"  |J(2*2*2*{n})| = {v}")

    # Interpolate polynomial.
    # But wait: is it really polynomial of degree 8?
    coeffs = interpolate_polynomial(values)
    # Check if it's really degree 8:
    # Compute a 10th value and compare.
    v10 = count_J((2, 2, 2, 10))
    # Evaluate polynomial at 10
    pv10 = sum(c * Fraction(10) ** i for i, c in enumerate(coeffs))
    print(f"  |J(2*2*2*10)| = {v10}, polynomial predicts {pv10}")
    assert pv10 == v10, "Polynomial fit failed"
    # Convert to binomial basis.
    bcoeffs = polynomial_in_binomial_basis(coeffs, 8)
    print(f"\n  In basis C(n+k, k): coefficients b_0, ..., b_8 =")
    for k, bk in enumerate(bcoeffs):
        print(f"    b_{k} = {bk}")
    # Berman-Koehler says: 48*C(n+8,8) - 96*C(n+7,7) + 63*C(n+6,6) - 15*C(n+5,5) + C(n+4,4).
    # So b_8 = 48, b_7 = -96, b_6 = 63, b_5 = -15, b_4 = 1, b_3=b_2=b_1=b_0 = 0.
    expected = {8: 48, 7: -96, 6: 63, 5: -15, 4: 1, 3: 0, 2: 0, 1: 0, 0: 0}
    for k, exp in expected.items():
        if bcoeffs[k] != exp:
            print(f"  MISMATCH at b_{k}: got {bcoeffs[k]}, expected {exp}")
        else:
            print(f"  OK b_{k} = {exp}")


def derive_22m_polynomial(m, verify_oeis=None):
    """Derive polynomial for |J(2*2*m*n)| of degree 4m."""
    print("=" * 70)
    print(f"Deriving |J(2*2*{m}*n)| polynomial (degree {4*m})")
    print("=" * 70)
    values = []
    deg = 4 * m
    for n in range(deg + 2):  # one extra for verification
        v = count_J((2, 2, m, n))
        # Note: for n=0 the poset is empty -> 1 ideal. Let's double-check by direct call.
        values.append(v)
        print(f"  |J(2*2*{m}*{n})| = {v}")
    # Interpolate using first deg+1 values.
    coeffs = interpolate_polynomial(values[: deg + 1])
    # Verify next value.
    n_next = deg + 1
    predicted = sum(c * Fraction(n_next) ** i for i, c in enumerate(coeffs))
    actual = values[deg + 1]
    print(f"\n  Verification: p({n_next}) = {predicted}, actual = {actual}")
    assert predicted == actual, f"Polynomial fit failed for m={m}"

    # Express in binomial basis.
    bcoeffs = polynomial_in_binomial_basis(coeffs, deg)
    print(f"\n  |J(2*2*{m}*n)| = ")
    terms = []
    for k in range(deg, -1, -1):
        if bcoeffs[k] != 0:
            print(f"    + ({bcoeffs[k]}) * C(n+{k}, {k})")
            terms.append((k, bcoeffs[k]))

    # Verify against OEIS if provided.
    if verify_oeis is not None:
        print(f"\n  OEIS cross-check:")
        for n, expected in verify_oeis.items():
            if n <= len(values) - 1:
                got = values[n]
            else:
                got = sum(c * Fraction(n) ** i for i, c in enumerate(coeffs))
            mark = "OK" if got == expected else "MISMATCH"
            print(f"    n={n}: {got} (OEIS: {expected}) [{mark}]")

    return coeffs, bcoeffs, values


def print_gf_numerator(bcoeffs, denom_power, label):
    """Convert binomial-basis to G.F. rational form with denominator (1-x)^denom_power."""
    from sympy import symbols, Poly, simplify
    x = symbols('x')
    gf = sum(bcoeffs[k] / (1 - x) ** (k + 1) for k in range(len(bcoeffs)) if bcoeffs[k] != 0)
    num = simplify(gf * (1 - x) ** denom_power).expand()
    p = Poly(num, x)
    coeffs_list = p.all_coeffs()[::-1]
    print(f"  {label} G.F. = N(x) / (1-x)^{denom_power}")
    print(f"    N(x) coefficients: {coeffs_list}")
    return coeffs_list


if __name__ == "__main__":
    run_222_check()
    print()
    # |J(2*2*3*n)| — OEIS A006360
    coeffs3, bcoeffs3, values3 = derive_22m_polynomial(3)
    print_gf_numerator(bcoeffs3, 13, "2*2*3*n")
    print()
    # |J(2*2*4*n)| — OEIS A006361
    coeffs4, bcoeffs4, values4 = derive_22m_polynomial(4)
    print_gf_numerator(bcoeffs4, 17, "2*2*4*n")
    print()
    # |J(2*2*5*n)| — OEIS A006362 (NO G.F. in OEIS!)
    coeffs5, bcoeffs5, values5 = derive_22m_polynomial(5)
    print_gf_numerator(bcoeffs5, 21, "2*2*5*n")
