"""
Test whether the A000712 = [q^n] 1/eta^2 universal-tail identification of
CAG on [m]^2 generalizes to other locally finite posets.

Method: for each poset P, enumerate all convex (order-convex) subsets,
bin them by size, and extract the tail CC_{|P|-k}(P) for small k. Compare
against η-product coefficients:
    1/η   = p(n)        = 1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, ...
    1/η²  = A000712     = 1, 2, 5, 10, 20, 36, 65, 110, 185, 300, 481, ...
    1/η³  = A000716     = 1, 3, 9, 22, 51, 108, 221, 429, 810, ...
    1/η⁴  = A001935     = 1, 4, 14, 40, 105, 252, 574, 1240, ...

If other posets give η-products (possibly with different exponents), the
modular-form structure is a real pattern. If only [m]^2 gives 1/η² and
other posets give random sequences, the original observation is coincidence.
"""

import math
from itertools import product as iproduct


# Partition-count sequences
INVETA1 = [1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176]      # A000041
INVETA2 = [1,2,5,10,20,36,65,110,185,300,481,752,1165,1770]    # A000712
INVETA3 = [1,3,9,22,51,108,221,429,810,1479,2640,4599]          # A000716
INVETA4 = [1,4,14,40,105,252,574,1240,2580,5180,10108]          # A001935
INVETA5 = [1,5,20,65,190,506,1265,2990,6765,14725]              # A023003


def is_convex(S_set, P_list, leq):
    """Check if S is order-convex: closed under betweenness."""
    S = list(S_set)
    for a in S:
        for b in S:
            if leq(a, b):
                for c in P_list:
                    if c not in S_set and leq(a, c) and leq(c, b):
                        return False
    return True


def count_convex_by_size(P_list, leq, size_limit=None):
    """Return list counts where counts[k] = # convex subsets of size k."""
    N = len(P_list)
    counts = [0] * (N + 1)
    for mask in range(1 << N):
        S_set = frozenset(P_list[i] for i in range(N) if (mask >> i) & 1)
        if is_convex(S_set, P_list, leq):
            counts[len(S_set)] += 1
    return counts


def grid_leq(d):
    def _leq(a, b):
        return all(ai <= bi for ai, bi in zip(a, b))
    return _leq


def grid_poset(dims):
    """Return (P, leq) for grid product of given dimensions."""
    P = list(iproduct(*[range(d) for d in dims]))
    return P, grid_leq(len(dims))


def boolean_poset(n):
    """Boolean lattice B_n: subsets of {0,...,n-1} under inclusion."""
    P = [frozenset(S) for S in iproduct([0, 1], repeat=n)
         for S in [tuple(i for i in range(n) if S[i])]]
    # dedupe
    P = [frozenset(i for i in range(n) if t[i]) for t in iproduct([0, 1], repeat=n)]
    def _leq(a, b):
        return a.issubset(b)
    return P, _leq


def divisibility_poset(N):
    """Divisibility poset on {1, ..., N}: a <= b iff a divides b."""
    P = list(range(1, N + 1))
    def _leq(a, b):
        return b % a == 0
    return P, _leq


def print_tail(name, counts, k_max=7):
    N = len(counts) - 1
    tail = [counts[N - k] for k in range(k_max + 1) if N - k >= 0]
    print(f"\n{name}: |P| = {N}")
    print(f"  Tail CC_{{|P|-k}} for k = 0..{len(tail)-1}:")
    print(f"    {tail}")
    # Compare with η-products
    for exp, seq in [(1, INVETA1), (2, INVETA2), (3, INVETA3), (4, INVETA4), (5, INVETA5)]:
        ref = seq[:len(tail)]
        match = (tail == ref)
        marker = "*** MATCH ***" if match else ""
        print(f"  vs 1/eta^{exp}: {ref[:len(tail)]}  {marker}")


def main():
    # Poset 1: [m]^2 (baseline — should match 1/eta^2)
    P, leq = grid_poset((4, 4))
    counts = count_convex_by_size(P, leq)
    print_tail("[4]^2 (16 elements)", counts)

    P, leq = grid_poset((5, 5))
    counts = count_convex_by_size(P, leq)
    print_tail("[5]^2 (25 elements, will be slow)", counts, k_max=7)

    # Poset 2: [m]^3
    P, leq = grid_poset((3, 3, 3))
    counts = count_convex_by_size(P, leq)
    print_tail("[3]^3 (27 elements)", counts, k_max=7)

    # Poset 3: rectangular grid [m] x [n]
    P, leq = grid_poset((3, 5))
    counts = count_convex_by_size(P, leq)
    print_tail("[3] x [5] (15 elements)", counts, k_max=7)

    P, leq = grid_poset((2, 7))
    counts = count_convex_by_size(P, leq)
    print_tail("[2] x [7] (14 elements)", counts, k_max=7)

    # Poset 4: Boolean lattice
    P, leq = boolean_poset(4)
    counts = count_convex_by_size(P, leq)
    print_tail("B_4 = Boolean(4) (16 elements)", counts, k_max=7)

    # Poset 5: Divisibility {1..N}
    for N in [12, 15]:
        P, leq = divisibility_poset(N)
        counts = count_convex_by_size(P, leq)
        print_tail(f"Divisibility on {{1..{N}}} ({N} elements)", counts, k_max=6)


if __name__ == "__main__":
    main()
