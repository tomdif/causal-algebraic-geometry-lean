"""
CAG on the divisibility poset: count convex subsets of {1, ..., N} under the
divisibility partial order (a ≤ b iff a divides b).

A subset S ⊆ {1, ..., N} is divisibility-convex iff for every a, b ∈ S with
a | b, every c with a | c and c | b is also in S. Equivalently: S contains
the full divisibility interval between any two comparable elements it already
contains.

Questions:
  1. What is |CC_div(N)| for small N?
  2. Is it in OEIS?
  3. Does log|CC_div(N)| have a growth rate tied to a known arithmetic
     constant (ζ(2), π²/6, a specific Dirichlet series evaluation, etc.)?
"""

import math
import time
from itertools import combinations


def divisors(n: int):
    """All positive divisors of n."""
    result = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            result.append(i)
            if i * i != n:
                result.append(n // i)
        i += 1
    return sorted(result)


def is_div_convex(S: frozenset) -> bool:
    """Test whether S ⊆ ℕ_+ is convex in the divisibility poset."""
    lst = sorted(S)
    for i, a in enumerate(lst):
        for b in lst[i + 1:]:
            if b % a == 0:
                # Divisibility interval [a, b] = {a * d : d divides b/a}.
                ratio = b // a
                for d in divisors(ratio):
                    c = a * d
                    if c not in S:
                        return False
    return True


def count_CC_div(N: int) -> int:
    """|CC_div(N)| via brute force over subsets of {1, ..., N}."""
    total = 0
    elements = list(range(1, N + 1))
    # Enumerate by bitmask
    for mask in range(1 << N):
        S = frozenset(e for i, e in enumerate(elements) if (mask >> i) & 1)
        if is_div_convex(S):
            total += 1
    return total


def main():
    print("CAG on divisibility poset: |CC_div(N)| for N = 1..")
    print()
    print(f"{'N':>3} {'|CC_div(N)|':>14} {'log|CC|':>10} "
          f"{'log|CC|/N':>10} {'log|CC|/(N log N)':>20} {'time (s)':>10}")

    results = {}
    for N in range(1, 21):
        t0 = time.time()
        c = count_CC_div(N)
        t1 = time.time()
        results[N] = c
        log_c = math.log(c) if c > 0 else 0.0
        norm_log = log_c / N if N > 0 else 0.0
        norm_log2 = log_c / (N * math.log(N)) if N > 1 else 0.0
        print(f"{N:>3} {c:>14} {log_c:>10.4f} "
              f"{norm_log:>10.5f} {norm_log2:>20.5f} {t1 - t0:>10.3f}")
        if t1 - t0 > 60:
            print("  (stopping: single-N takes >60s)")
            break

    # Print just the raw sequence for OEIS submission
    print()
    print("Raw sequence |CC_div(N)| for N = 1, 2, 3, ...:")
    print(", ".join(str(results[N]) for N in sorted(results)))


if __name__ == "__main__":
    main()
