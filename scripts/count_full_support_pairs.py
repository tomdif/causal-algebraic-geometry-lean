"""
Count full-support antitone pairs on [m]^2 → [0, m].

Q(m) := #{(φ, ψ) : [m]² → [0,m] antitone, φ(i,j) < ψ(i,j) pointwise}

Comparison targets:
  - L_3  = (9/2) ln 3 - 6 ln 2 ≈ 0.7849
  - 2L_3 ≈ 1.5697
  - If log Q(m)/m² → 2 L_3, the full-support pathway closes c_3 = 2 L_3.
  - If log Q(m)/m² → L_3, the pathway is too weak (trivial lower bound).
  - PP(m,m,m) := #{antitone [m]² → [0,m]} — MacMahon box count.
"""

import math
import sys


def nonincreasing_rows(length, max_val):
    """All non-increasing sequences of `length` with entries in [0, max_val]."""
    if length == 0:
        yield ()
        return
    for v in range(max_val, -1, -1):
        for rest in nonincreasing_rows(length - 1, v):
            yield (v,) + rest


def antitone_funcs(m, max_val):
    """All antitone functions [m]² → [0, max_val], as tuples of m rows."""
    all_rows = list(nonincreasing_rows(m, max_val))

    def build(prefix, depth):
        if depth == m:
            yield prefix
            return
        if depth == 0:
            for r in all_rows:
                yield from build((r,), 1)
        else:
            prev = prefix[-1]
            for r in all_rows:
                if all(r[j] <= prev[j] for j in range(m)):
                    yield from build(prefix + (r,), depth + 1)

    yield from build((), 0)


def count_Q(m):
    """Brute-force count of full-support antitone pairs on [m]² → [0,m]."""
    ats = list(antitone_funcs(m, m))
    n_pp = len(ats)
    count = 0
    for psi in ats:
        for phi in ats:
            ok = True
            for i in range(m):
                for j in range(m):
                    if phi[i][j] >= psi[i][j]:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                count += 1
    return count, n_pp


def main():
    L3 = 4.5 * math.log(3) - 6 * math.log(2)
    print(f"L_3 = (9/2)ln 3 - 6 ln 2 = {L3:.6f}")
    print(f"2 L_3 = {2 * L3:.6f}")
    print()
    print(f"{'m':>3} {'PP(m,m,m)':>12} {'Q(m)':>14} "
          f"{'lnQ/m²':>9} {'lnPP/m²':>9} {'lnQ/lnPP':>9}")
    print("-" * 64)
    for m in range(1, 4):
        q, n_pp = count_Q(m)
        lnQ = math.log(q) if q > 0 else 0.0
        lnPP = math.log(n_pp) if n_pp > 0 else 0.0
        print(f"{m:>3} {n_pp:>12} {q:>14} "
              f"{lnQ/m**2:>9.4f} {lnPP/m**2:>9.4f} "
              f"{(lnQ/lnPP if lnPP > 0 else 0):>9.4f}", flush=True)


if __name__ == "__main__":
    main()
