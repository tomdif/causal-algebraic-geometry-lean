"""
Extract the explicit polynomial formula for |J(2*3*4*n)| = A056936(n)
via Berman-Koehler's Corollary 3.2 iterated transfer matrix.

|J(2*3*4*n)| is a polynomial in n of degree |2*3*4| = 24.

State space: order ideals of the 3D product 2*3*4, |S(2*3*4)| = 490.
Transitions: I' covers I iff I' ⊆ I (order ideal containment).
Recurrence: |J(2*3*4*[n])| = sum over chains of length n in J(2*3*4).

At n=4, the polynomial must reproduce Q(4) = 89,613,429
(the diagonal point of our full-support pair count).

At n=0..14, must match OEIS A056936 b-file.
"""

import sys
from fractions import Fraction
from itertools import product as iproduct


def enumerate_order_ideals_3d(a, b, c):
    """
    Order ideals of [a] x [b] x [c] (product of chains).
    Each order ideal is determined by a monotone non-increasing
    height profile h : [a] x [b] -> {0, 1, ..., c}
    where h(i,j) >= h(i',j') when i <= i' and j <= j'
    (so smaller coordinates have larger heights).

    Encode as tuple of tuples for hashing.
    """
    # Generate all weakly decreasing profiles using DP
    # Simpler: enumerate recursively, choosing heights with constraints.

    ideals = []

    # Flatten ordering: traverse (i, j) in some order; constraint is
    # h(i, j) >= h(i+1, j) and h(i, j) >= h(i, j+1)
    # which means given h(i+1, j) and h(i, j+1), we must have h(i, j) >= max.

    def rec(profile, idx_flat):
        if idx_flat == a * b:
            # profile is complete
            # Convert to tuple of tuples
            prof_tuple = tuple(
                tuple(profile[i * b + j] for j in range(b))
                for i in range(a)
            )
            ideals.append(prof_tuple)
            return
        # Next cell at (i, j)
        i, j = divmod(idx_flat, b)
        # Constraints:
        #   h(i, j) >= h(i+1, j) if i+1 < a
        #   h(i, j) >= h(i, j+1) if j+1 < b
        # But we visit in row-major order: profile[i*b + j] comes BEFORE
        # profile[(i+1)*b + j] and profile[i*b + j+1].
        # So we need constraints from PRIOR cells: (i-1, j) and (i, j-1).
        # h(i, j) <= h(i-1, j) if i > 0
        # h(i, j) <= h(i, j-1) if j > 0
        max_h = c
        if i > 0:
            max_h = min(max_h, profile[(i - 1) * b + j])
        if j > 0:
            max_h = min(max_h, profile[i * b + (j - 1)])
        for h in range(max_h + 1):
            profile.append(h)
            rec(profile, idx_flat + 1)
            profile.pop()

    rec([], 0)
    return ideals


def transition_count(X_ideals):
    """
    Build transition: dict from ideal I to count of (ideal J with J ⊆ I).
    Actually for the Berman-Koehler recurrence, we want:
      |S(I * [n])| = sum_{J ⊆ I} |S(J * [n-1])|

    We return a list of (I_index, [J_indices where J ⊆ I]).
    """
    N = len(X_ideals)
    idx_of = {I: i for i, I in enumerate(X_ideals)}

    # Precompute containment: J ⊆ I iff J(i,j) <= I(i,j) for all (i,j)
    a = len(X_ideals[0])
    b = len(X_ideals[0][0])
    containment = [[] for _ in range(N)]  # containment[i] = [j : ideals[j] ⊆ ideals[i]]
    for i_i, I in enumerate(X_ideals):
        for j_j, J in enumerate(X_ideals):
            ok = True
            for ii in range(a):
                for jj in range(b):
                    if J[ii][jj] > I[ii][jj]:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                containment[i_i].append(j_j)
    return containment


def compute_J_values(a, b, c, n_max):
    """Compute |J(a*b*c*[n])| for n = 0, 1, ..., n_max."""
    X_ideals = enumerate_order_ideals_3d(a, b, c)
    N = len(X_ideals)
    print(f"|S({a}*{b}*{c})| = {N}", file=sys.stderr)

    containment = transition_count(X_ideals)

    # f_n[I] = |S(I * [n])|
    # Recurrence: f_n[I] = sum_{J ⊆ I} f_{n-1}[J]
    # f_0[I] = 1 for all I (no levels means just the empty ideal chain)
    f = [1] * N
    values = []
    # |J(a*b*c*[n])| = sum over I of f_n[I] ... wait no.
    # Let me re-derive.
    # |S(X * [n])| = sum_I |S(I * [n-1])| where I ranges over S(X).
    # Let g_n[I] := |S(I * [n])|.
    # g_0[I] = 1 (the only ideal of I * [0] = I * empty is the whole empty ideal... wait)
    # Hmm. Let me re-think.
    # |S(X * [n])| where [n] is a chain of n elements (for n>=1).
    # For n=1: X * [1] is just X with one extra top element? Or [1] is a single element?
    # Convention: [n] in B-K means n-element chain.
    # Order ideals of X * [1] where [1] is singleton: each ideal of X * [1] is
    # either empty-extension of ideal of X, or full-extension plus singleton.
    # Actually X * [1] = X * {*} = X (with one extra element above everything? no, chain of 1 = single element).
    # [1] singleton: X * [1] = X x {0}. Order ideals = order ideals of X.
    # So |S(X * [1])| = |S(X)|.
    # For n=2: X * [2] = X x {0, 1}. An ideal is (I_0, I_1) with I_1 ⊆ I_0 (since 1 > 0 in [2]).
    # |S(X * [2])| = sum_{I_0} |{I_1 : I_1 ⊆ I_0}|. Each I_1 is an ideal of I_0 viewed as a subposet.
    # = sum_{I_0} |S(I_0)| (where S(I_0) = ideals of the subposet I_0).
    # Hmm, but I_0 is an order ideal of X; its ideals are ideals of X contained in I_0.
    # Equivalently: |S(X * [2])| = number of PAIRS (I_0, I_1) with I_1 ⊆ I_0.
    # By Cor 3.2: |S(X * [n])| = sum_{I in S(X)} |S(I * [n-1])|.
    # Base: |S(X * [0])| = 1 (only ideal is empty; [0] = empty chain, so X * [0] = empty).
    # Wait, [0] empty, X * [0] empty, |S(empty)| = 1.

    # Actually let's redefine cleanly:
    # For n >= 0, and for each ideal I of X, define g_n[I] := |S(I * [n])|.
    # Then g_0[I] = 1 for all I (the empty ideal of the empty poset).
    # g_n[I] = sum_{J ⊆ I, J ideal of X} g_{n-1}[J]  (by recursive Cor 3.2)
    # Note I is an ideal of X, J ⊆ I is also an ideal of X (since J is an ideal of the subposet I, which equals J as an ideal of X when J ⊆ I).

    # Then |J(X * [n])| = g_n[X_full_ideal] where X_full_ideal corresponds to
    # the "largest" ideal = all of X. But wait, we want |S(X * [n])| where X here is the 3D base and [n] is the extra chain.
    # |S(X * [n])| = sum over all (I_{n-1} ⊆ I_{n-2} ⊆ ... ⊆ I_0) of 1 where each I_k is an ideal of X.
    # = number of chains of length n (incl possibly-equal) in J(X).
    # This is N^n if no constraints, but constrained by containment.
    # Recursion: g_n = |chain-count ending at I_n = I| starting from any I_0.
    # Sum: |S(X*[n])| = sum_I g_n[I] where g_n[I] = count of chains (I_0,...,I_{n-1},I) with I_{n-1} ⊆ ... ⊆ I_0.
    # Wait I'm confusing myself. Let me restart.

    # Number of order ideals of X * [n] where X * [n] is the 4D poset.
    # An order ideal of X * [n] is a subset S that's downward closed.
    # Restricting S to each "level" k = 0, 1, ..., n-1 (fibers of [n]) gives
    # a family of ideals of X, which must be nested.
    # Specifically: S_k := {x ∈ X : (x, k) ∈ S} is an ideal of X, and
    # S_0 ⊇ S_1 ⊇ ... ⊇ S_{n-1} (since (x, k) ∈ S implies (x, k') ∈ S for k' < k).
    # So |S(X * [n])| = |{(I_0, I_1, ..., I_{n-1}) : I_0 ⊇ I_1 ⊇ ... ⊇ I_{n-1}}|.
    # = number of weakly decreasing chains of ideals of X of length n.

    # DP: let f_k[I] = # chains (I_0 ⊇ ... ⊇ I_{k-1} = I) of length k ending at I.
    # f_1[I] = 1 for all I (chain of length 1 ending at I is just (I)).
    # f_k[I] = sum_{J ⊇ I} f_{k-1}[J].
    # Then |S(X * [n])| = sum_I f_n[I].

    # Transition: J ⊇ I in our containment list.
    # containment[i] = [j : ideals[j] ⊆ ideals[i]]
    # So for DP, f_k[i] = sum over j with j ⊇ i of f_{k-1}[j]
    # = sum over j with containment[j] contains i of f_{k-1}[j].
    # Or: build reverse containment: supersets[i] = [j : ideals[i] ⊆ ideals[j]].

    supersets = [[] for _ in range(N)]
    for j, subs in enumerate(containment):
        for i in subs:
            supersets[i].append(j)

    # Start with f_0[I] = 1 (chain of length 0 ending at I; empty chain convention).
    # Then f_{k+1}[I] = sum_{J ⊇ I} f_k[J]

    # Actually the recurrence |S(X * [n])| = sum over chains (I_0 ⊇ ... ⊇ I_{n-1}) naturally has
    # length n, and we want this count.
    # Take f_1[I] = 1 (chain of length 1: just I). Then f_k+1[I] = sum_{J ⊇ I} f_k[J].
    # Total count at level n: sum_I f_n[I].

    # Or equivalently: |J(X * [n])| = (1^T * M^{n-1} * 1) where M is the supersets adjacency.
    # For n=0: conv is |J(X * empty)| = 1. Total = 1.
    # For n=1: |J(X)| = N. Total = N (= sum of f_1).

    values = [1, N]  # n = 0, 1
    f = [1] * N  # f_1[I] = 1

    for k in range(2, n_max + 1):
        f_new = [0] * N
        for i in range(N):
            # f_new[i] = sum over j in supersets[i] of f[j]
            total = 0
            for j in supersets[i]:
                total += f[j]
            f_new[i] = total
        f = f_new
        values.append(sum(f))

    return values


def lagrange_interpolate(x_values, y_values):
    """Return polynomial coefficients (from constant to highest-deg) of
    the unique polynomial p of degree <= n-1 with p(x_i) = y_i.
    Uses Fraction arithmetic for exact coefficients."""
    n = len(x_values)
    assert len(y_values) == n
    # Barycentric form is simpler; we do naive Lagrange.
    coeffs = [Fraction(0)] * n
    for i in range(n):
        # Li(x) = prod_{j != i} (x - x_j) / (x_i - x_j)
        # Numerator polynomial:
        num = [Fraction(1)]
        denom = Fraction(1)
        for j in range(n):
            if j == i:
                continue
            new_num = [Fraction(0)] * (len(num) + 1)
            for k in range(len(num)):
                new_num[k] -= num[k] * Fraction(x_values[j])
                new_num[k + 1] += num[k]
            num = new_num
            denom *= Fraction(x_values[i] - x_values[j])
        # Li(x) * y_i, add to coeffs
        for k in range(len(num)):
            coeffs[k] += num[k] * Fraction(y_values[i]) / denom
    return coeffs


def evaluate_poly(coeffs, x):
    result = Fraction(0)
    for i, c in enumerate(coeffs):
        result += c * Fraction(x) ** i
    return result


def main():
    a, b, c = 2, 3, 4
    n_max = 30  # need at least 25 for degree-24 polynomial
    values = compute_J_values(a, b, c, n_max)

    print(f"Computed |J({a}*{b}*{c}*[n])| for n = 0..{n_max}:")
    for n in range(min(len(values), 20)):
        print(f"  n={n:>2}: {values[n]}")
    print()

    # Validate against OEIS A056936 first 15 values
    A056936 = [1, 490, 59542, 3092808, 89613429, 1691136270, 22954776044,
               239831111938, 2024703039198, 14318216628378, 87184226214168,
               467034400160664, 2239064967256060, 9741467994941264,
               38902816410160608]
    print("Validation vs OEIS A056936:")
    for n in range(len(A056936)):
        got = values[n]
        exp = A056936[n]
        ok = "✓" if got == exp else "FAIL"
        print(f"  n={n:>2}: computed {got}, OEIS {exp}  {ok}")
    print()

    # Verify Q(4) = A056936(4) = 89,613,429
    Q4 = values[4]
    print(f"Q(4) via this method: {Q4}")
    print(f"Expected Q(4): 89,613,429 (matches: {Q4 == 89613429})")
    print()

    # Interpolate polynomial of degree 24 from values n = 0..24
    print("Interpolating polynomial of degree 24 from values n=0..24...")
    xs = list(range(25))
    ys = values[:25]
    coeffs = lagrange_interpolate(xs, ys)
    # Display leading + constant
    print(f"Leading coefficient (x^24): {coeffs[24]}")
    print(f"Constant term: {coeffs[0]}")
    # Verify at extra points
    for n_test in range(25, min(len(values), 30)):
        pred = evaluate_poly(coeffs, n_test)
        actual = Fraction(values[n_test])
        ok = "✓" if pred == actual else "FAIL"
        print(f"  Extrapolated at n={n_test}: pred={pred}, actual={actual}  {ok}")

    # Express in C(n+k, k) basis: standard reformulation for OEIS output
    # (a(n) = sum a_k * C(n+k, k) for various k)
    # This is more technical; skip for now.


if __name__ == "__main__":
    main()
