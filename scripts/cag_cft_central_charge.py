"""
Test whether 2D CAG on a rectangular box [m] × [L] behaves like a c=2 CFT.

Approach: compute |CC([m] × [L])| exactly via a corrected transfer matrix
(state = (current column fiber, last nonempty column fiber), since simple
pairwise TM misses convexity constraints across empty middle columns).

Then check two CFT signatures:

1. Bulk + boundary decomposition:
   log Z(m, L) = f_bulk · m·L + f_boundary·(m + L) + c_corner + O(log)
   For a c=2 CFT on a torus/cylinder, there's a universal log correction
   tied to the central charge.

2. Thin-strip limit (L ≫ m):
   log Z(m, L) ≈ f(m) · L with f(m) = f_bulk · m + π·c/(6 · effective_width) + ...
   For c=2, the subleading 1/m piece should give c/6 = 1/3 times π.
"""

import math
import time
from itertools import product as iproduct

import numpy as np


def column_fibers(L):
    """All fibers: empty + intervals [l, u] with 0 ≤ l ≤ u < L."""
    fibers = [None]  # None represents empty
    for l in range(L):
        for u in range(l, L):
            fibers.append((l, u))
    return fibers


def allowed(prev_lnp, gap, curr):
    """Transition rule with gap tracking.

    prev_lnp: most recent non-empty fiber, or None.
    gap: was the immediately previous column empty? (boolean)
    curr: current column fiber (None for empty, or (l, u)).

    Rule:
      * curr empty: always OK.
      * curr = (l, u) and prev_lnp = None: OK.
      * curr = (l, u), prev_lnp = (lL, uL), gap = False (adjacent): OK iff
        l <= lL and u <= uL.
      * curr = (l, u), prev_lnp = (lL, uL), gap = True (empties between):
        OK iff l > uL (strict disjoint, col-below relation). Otherwise the
        intervening empty columns would violate convexity.
    """
    if curr is None:
        return True
    if prev_lnp is None:
        return True
    lL, uL = prev_lnp
    l, u = curr
    if gap:
        return lL > u
    return l <= lL and u <= uL


def count_CC(m: int, L: int) -> int:
    """|CC([m] × [L])| via corrected transfer matrix."""
    fibers = column_fibers(L)
    nonempty_fibers = [f for f in fibers if f is not None]
    # State: (last_nonempty_fiber, gap_bool).
    # last_nonempty_fiber can be None (no nonempty col seen yet).
    # gap_bool = True iff immediately previous column was empty
    # (equivalently, there's been an empty column since the last nonempty).
    states = []
    for lnp in [None] + nonempty_fibers:
        for gap in [False, True]:
            if lnp is None and gap:
                continue  # redundant; no nonempty seen yet
            states.append((lnp, gap))
    state_idx = {s: i for i, s in enumerate(states)}
    n = len(states)

    # Initial: no columns processed. lnp = None, gap = False.
    v = np.zeros(n, dtype=object)
    v[state_idx[(None, False)]] = 1

    for _col in range(m):
        v_new = np.zeros(n, dtype=object)
        for i, (lnp, gap) in enumerate(states):
            if v[i] == 0:
                continue
            for curr in fibers:
                if not allowed(lnp, gap, curr):
                    continue
                if curr is None:
                    # column is empty
                    new_lnp = lnp
                    new_gap = True if lnp is not None else False
                else:
                    new_lnp = curr
                    new_gap = False
                new_state = (new_lnp, new_gap)
                v_new[state_idx[new_state]] += v[i]
        v = v_new
    return int(sum(v))


def main():
    print("2D CAG on [m] × [L] box, exact counts.\n")
    print(f"{'m':>3} {'L':>3} {'|CC|':>14} {'log|CC|':>10} "
          f"{'log|CC|/(mL)':>14} {'log|CC|/L':>12}")
    results = {}
    for m in range(2, 8):
        for L in range(2, 12):
            if m > 6 and L > 8:
                continue
            t0 = time.time()
            c = count_CC(m, L)
            t1 = time.time()
            if t1 - t0 > 60:
                break
            results[(m, L)] = c
            logc = math.log(c)
            print(f"{m:>3} {L:>3} {c:>14} {logc:>10.4f} "
                  f"{logc/(m*L):>14.5f} {logc/L:>12.5f}")
    print()

    # Sanity check: diagonal |CC([m]²)| matches known values
    print("Diagonal sanity check:")
    expected = {2: 13, 3: 114, 4: 1146}
    for m in sorted(set(key[0] for key in results)):
        if (m, m) in results and m in expected:
            got = results[(m, m)]
            exp = expected[m]
            ok = "✓" if got == exp else "FAIL"
            print(f"  |CC([{m}]²)| = {got} expected {exp}  {ok}")

    # Bulk-boundary fit: log Z = a·m·L + b·(m + L) + c
    print()
    print("Fit log Z(m, L) = a·m·L + b·(m + L) + c + d·log(m·L):")
    ms, Ls, ys = [], [], []
    for (m, L), cval in results.items():
        if m >= 3 and L >= 3:
            ms.append(m)
            Ls.append(L)
            ys.append(math.log(cval))
    ms = np.array(ms, dtype=float)
    Ls = np.array(Ls, dtype=float)
    ys = np.array(ys)
    # columns: m·L, m+L, 1, log(m·L)
    A = np.vstack([ms * Ls, ms + Ls, np.ones_like(ms),
                   np.log(ms * Ls)]).T
    params, *_ = np.linalg.lstsq(A, ys, rcond=None)
    a, b, c, d = params
    pred = A @ params
    r2 = 1 - np.sum((ys - pred) ** 2) / np.sum((ys - ys.mean()) ** 2)
    print(f"  bulk coefficient a = {a:.5f}   (log|CC|/mL at large mL)")
    print(f"  boundary b        = {b:+.5f}")
    print(f"  constant c        = {c:+.5f}")
    print(f"  log coefficient d = {d:+.5f}   "
          f"(compare c_CFT/6 = 1/3 ≈ 0.333 for c=2)")
    print(f"  R²                = {r2:.6f}")
    print()

    # Strip limit: log Z(m, L) as L ≫ m.
    print("Thin-strip limit: f(m) := lim_{L→∞} log|CC([m]×[L])|/L")
    for m in sorted(set(key[0] for key in results)):
        Ls_for_m = sorted(L for (mm, L) in results if mm == m)
        if len(Ls_for_m) >= 4:
            xs = np.array(Ls_for_m, dtype=float)
            ys = np.array([math.log(results[(m, L)]) for L in Ls_for_m])
            # Fit log Z = f·L + g + h·log(L)
            B = np.vstack([xs, np.ones_like(xs), np.log(xs)]).T
            slope, intercept, log_coef = np.linalg.lstsq(B, ys, rcond=None)[0]
            print(f"  m={m}: f(m)={slope:.5f}, g={intercept:.3f}, "
                  f"log-coef={log_coef:+.4f}")


if __name__ == "__main__":
    main()
