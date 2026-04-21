"""
Casimir-scaling test for CAG on a rectangular box [a] x [L].

Q: does log |CC([a] x [L])| contain a subleading term of the form
   −α · L / a^(D−1) = −α · L / a  (for D = 2, i.e., 2D CAG)
that would mirror the Casimir energy per unit transverse length
between parallel "plates" at separation `a`?

Method: compute |CC([a] x [L])| exactly via a transfer matrix whose
states are column fibers (intervals [l, u] with 0 ≤ l ≤ u < L, plus
an "empty" state). Pairwise transition rule for 2D product-order
convexity: non-empty columns with overlapping ranges require lower and
upper boundaries to both be non-increasing in the column index; non-
overlapping ranges (one strictly above the other, in the column-value
sense) impose no constraint; either column empty is always allowed.

Fit log |CC([a] x [L])| ≈ α(a) L + β(a) at large L. Then inspect α(a)
and β(a) as functions of a for a 1/a^(D−1) = 1/a signature.
"""

import math
from itertools import product as iproduct

import numpy as np


def column_states(L):
    """All possible column fibers: [l, u] with 0 <= l <= u < L, plus 'empty'."""
    states = [("E",)]  # empty sentinel
    for l in range(L):
        for u in range(l, L):
            states.append((l, u))
    return states


def allowed_transition(s0, s1):
    """Pairwise convexity constraint between adjacent column fibers.

    If both non-empty: need lower and upper boundaries both non-increasing
    from column i to i+1 (l1 <= l0 AND u1 <= u0). This handles both the
    overlap case and the correct disjoint case (column 1 strictly below
    column 0). The other disjoint case (column 0 strictly below column 1)
    is correctly blocked because it violates u1 <= u0.
    """
    if s0 == ("E",) or s1 == ("E",):
        return True
    l0, u0 = s0
    l1, u1 = s1
    return (l1 <= l0) and (u1 <= u0)


def count_CC_rect(a, L):
    """|CC([a] x [L])| via transfer matrix in the column direction."""
    states = column_states(L)
    N = len(states)
    # v[i] counts paths ending in state i over the current column index.
    v = [1] * N
    for _step in range(a - 1):
        v_new = [0] * N
        for j, sj in enumerate(states):
            total = 0
            for i, si in enumerate(states):
                if allowed_transition(si, sj):
                    total += v[i]
            v_new[j] = total
        v = v_new
    return sum(v)


def main():
    print("CAG on rectangular box [a] x [L], exact transfer-matrix count.\n")
    # Build table
    a_values = list(range(1, 9))
    L_values = list(range(1, 17))
    table = {}
    for a in a_values:
        for L in L_values:
            if L ** 2 * a > 2000:  # keep per-cell cost bounded
                continue
            table[(a, L)] = count_CC_rect(a, L)

    # Print table of log |CC|
    header = "a|L"
    print(f"{header:>3}", end="")
    for L in L_values:
        print(f"{L:>11}", end="")
    print()
    for a in a_values:
        print(f"{a:>3}", end="")
        for L in L_values:
            v = table.get((a, L))
            if v is None:
                print(f"{'-':>11}", end="")
            else:
                print(f"{math.log(v):>11.4f}", end="")
        print()
    print()

    # For each a, fit log |CC([a] x [L])| = alpha(a) * L + beta(a) over the
    # largest available L window.
    print(f"{'a':>3} {'alpha(a)':>10} {'beta(a)':>10} "
          f"{'L_range':>12} {'R^2':>8}")
    fits = {}
    for a in a_values:
        Ls = [L for L in L_values if (a, L) in table]
        if len(Ls) < 4:
            continue
        # Use tail of L values to avoid low-L transient
        keep = Ls[-min(8, len(Ls)):]
        xs = np.array(keep, dtype=float)
        ys = np.array([math.log(table[(a, L)]) for L in keep])
        slope, intercept = np.polyfit(xs, ys, 1)
        pred = slope * xs + intercept
        ss_res = np.sum((ys - pred) ** 2)
        ss_tot = np.sum((ys - ys.mean()) ** 2)
        r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0.0
        fits[a] = (slope, intercept)
        print(f"{a:>3} {slope:>10.5f} {intercept:>10.5f} "
              f"{str(keep[0])+'..'+str(keep[-1]):>12} {r2:>8.6f}")
    print()

    # Inspect alpha(a) and beta(a) for 1/a signatures
    print("Looking for Casimir-like 1/a dependence in alpha(a) and beta(a):")
    print()
    print(f"{'a':>3} {'alpha(a)':>10} {'alpha(a) - alpha(a-1)':>23} "
          f"{'beta(a)':>10} {'beta(a) * a':>12} {'beta(a) * a^2':>14}")
    as_sorted = sorted(fits)
    prev_alpha = None
    for a in as_sorted:
        alpha, beta = fits[a]
        d_alpha = f"{alpha - prev_alpha:>23.5f}" if prev_alpha is not None else f"{'':>23}"
        print(f"{a:>3} {alpha:>10.5f} {d_alpha} "
              f"{beta:>10.5f} {beta*a:>12.5f} {beta*a*a:>14.5f}")
        prev_alpha = alpha
    print()
    print("Interpretation:")
    print("  * alpha(a) ~ c * a  (linear in a) => log|CC| ~ c * a * L, a bulk-area scaling.")
    print("  * alpha(a) -> const as a -> inf  => plate-area scaling (Casimir-candidate).")
    print("  * beta(a) ~ -C/a  => log|CC| has subleading -C*L/a term, a Casimir signature.")
    print("  * beta(a) * a -> const  <=> Casimir-shape present in the beta constant term.")
    print()
    print("Note: this uses 2D product-order convexity (boundary condition = box walls).")
    print("'Parallel plates' here means the two sides x=0 and x=a-1 of the [a] direction.")


if __name__ == "__main__":
    main()
