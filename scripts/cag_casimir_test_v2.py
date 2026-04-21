"""
Casimir-scaling test v2. Uses BRUTE-FORCE enumeration over slab pairs
(lower, upper) of length a with values in [0, L], checking full convexity
directly. No TM shortcut — the TM in v1 had a bug around empty middle
columns, and for the Casimir question we only need small (a, L) anyway.

A 2D convex subset of [a] x [L] in the product order biject with pairs
(l, u) of length-a integer sequences where:
  - each column is either empty (sentinel l_i = L, u_i = -1), or
    0 ≤ l_i ≤ u_i < L.
  - convexity: for every pair i < i' with both non-empty and l_i ≤ u_{i'}
    (ranges comparable / overlap or column i below column i'), every
    intermediate column i'' has [l_i, u_{i'}] ⊆ [l_{i''}, u_{i''}] and the
    outer constraints l_i ≥ l_{i'} and u_i ≥ u_{i'} hold.

We enumerate all (l, u) candidate slab pairs and verify convexity of the
induced set by direct rectangle check. Slow but unambiguous.
"""

import math
from itertools import product as iproduct

import numpy as np


def induced_set(l, u, a, L):
    S = set()
    for i in range(a):
        if l[i] <= u[i]:
            for j in range(l[i], u[i] + 1):
                S.add((i, j))
    return S


def is_convex_set(S, a, L):
    S_set = set(S)
    for p in S_set:
        for q in S_set:
            if p == q:
                continue
            if all(pi <= qi for pi, qi in zip(p, q)):
                for r in iproduct(range(p[0], q[0] + 1),
                                  range(p[1], q[1] + 1)):
                    if r not in S_set:
                        return False
    return True


def count_CC_rect(a, L):
    """|CC([a] x [L])| via brute-force over all 2^(aL) subsets."""
    N = a * L
    points = [(i, j) for i in range(a) for j in range(L)]
    count = 0
    for mask in range(1 << N):
        S = [points[k] for k in range(N) if (mask >> k) & 1]
        if is_convex_set(S, a, L):
            count += 1
    return count


def main():
    # Small cases: a*L ≤ 16
    pairs = []
    for a in range(1, 9):
        for L in range(1, 20):
            if a * L <= 16:
                pairs.append((a, L))

    table = {}
    for a, L in pairs:
        table[(a, L)] = count_CC_rect(a, L)

    print("a L  |CC([a]x[L])|  log|CC|")
    for a, L in sorted(pairs, key=lambda p: (p[0], p[1])):
        c = table[(a, L)]
        print(f"{a:>2}{L:>3}  {c:>13} {math.log(c):>8.4f}")
    print()

    # For each a, fit log|CC| = alpha(a) L + beta(a) over the largest L window
    print("Fits log|CC([a]x[L])| ≈ alpha(a) L + beta(a):")
    print(f"{'a':>3} {'n_pts':>6} {'alpha(a)':>10} {'beta(a)':>10} {'R^2':>8}")
    fits = {}
    for a in range(1, 9):
        Ls = sorted([L for L in range(1, 20) if (a, L) in table])
        if len(Ls) < 3:
            continue
        xs = np.array(Ls, dtype=float)
        ys = np.array([math.log(table[(a, L)]) for L in Ls])
        slope, intercept = np.polyfit(xs, ys, 1)
        pred = slope * xs + intercept
        r2 = 1 - np.sum((ys - pred) ** 2) / max(np.sum((ys - ys.mean()) ** 2), 1e-12)
        fits[a] = (slope, intercept, len(Ls))
        print(f"{a:>3} {len(Ls):>6} {slope:>10.5f} {intercept:>10.5f} {r2:>8.4f}")
    print()

    # Casimir signature check
    print("alpha(a) and beta(a) shape analysis:")
    print(f"{'a':>3} {'alpha(a)':>10} {'Δalpha':>10} "
          f"{'beta(a)':>10} {'beta(a)·a':>12} {'beta(a)·a^2':>14}")
    prev_alpha = None
    for a in sorted(fits):
        alpha, beta, _ = fits[a]
        d = f"{alpha - prev_alpha:>10.5f}" if prev_alpha is not None else f"{'':>10}"
        print(f"{a:>3} {alpha:>10.5f} {d} "
              f"{beta:>10.5f} {beta*a:>12.5f} {beta*a*a:>14.5f}")
        prev_alpha = alpha
    print()
    print("If alpha(a) grows linearly in a: bulk-area scaling, not Casimir.")
    print("If alpha(a) -> const and beta(a) ~ -C/a: Casimir signature.")


if __name__ == "__main__":
    main()
