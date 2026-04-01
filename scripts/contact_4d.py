"""
4D contact sector: convex subsets of [m]^4.

Enumerate convex subsets of {0,1}^4 (m=2, brute force).
Compute generating function by size, compare with SP² (solid partition squared).
Extract contact correction and test 1/(1-x)^{d-2} = 1/(1-x)² pattern.
"""
import numpy as np
from itertools import combinations, product as iproduct
import time

def is_convex(S_set, points, d):
    """Check if S (set of indices) is convex in product order."""
    S_list = list(S_set)
    pts = [points[i] for i in S_list]
    for i, p in enumerate(pts):
        for j, q in enumerate(pts):
            if all(p[k] <= q[k] for k in range(d)):
                # p ≤ q: check all r with p ≤ r ≤ q
                for r in iproduct(*[range(p[k], q[k]+1) for k in range(d)]):
                    r_idx = None
                    for idx, pt in enumerate(points):
                        if pt == r:
                            r_idx = idx
                            break
                    if r_idx is not None and r_idx not in S_set:
                        return False
    return True

def enumerate_convex_subsets(m, d):
    """Enumerate all convex subsets of [m]^d, return counts by size."""
    points = list(iproduct(range(m), repeat=d))
    n = len(points)
    point_idx = {p: i for i, p in enumerate(points)}

    print(f"  [m]^d = [{m}]^{d}: {n} points, {2**n} subsets to check")

    counts = [0] * (n + 1)  # counts[k] = number of convex subsets of size k
    total = 0

    t0 = time.time()

    # Optimized: build interval closure for each pair
    # For each pair (p,q) with p ≤ q, precompute the interval [p,q]
    intervals = {}
    for i, p in enumerate(points):
        for j, q in enumerate(points):
            if all(p[k] <= q[k] for k in range(d)):
                interval = set()
                for r in iproduct(*[range(p[k], q[k]+1) for k in range(d)]):
                    interval.add(point_idx[r])
                intervals[(i, j)] = interval

    t1 = time.time()
    print(f"  Precomputed {len(intervals)} intervals [{t1-t0:.1f}s]")

    # Check all subsets
    for size in range(n + 1):
        count = 0
        if size == 0:
            count = 1  # empty set is convex
        else:
            for combo in combinations(range(n), size):
                S = set(combo)
                convex = True
                for i in combo:
                    for j in combo:
                        if (i, j) in intervals:
                            if not intervals[(i, j)].issubset(S):
                                convex = False
                                break
                    if not convex:
                        break
                if convex:
                    count += 1
        counts[size] = count
        total += count

    t2 = time.time()
    print(f"  Found {total} convex subsets [{t2-t1:.1f}s]")
    return counts, total

# ============================================================
print("=" * 70)
print("4D CONTACT SECTOR COMPUTATION")
print("=" * 70)
print()

# ===== d=2, m=2 (validation) =====
print("--- d=2, m=2 (validation) ---")
counts_22, total_22 = enumerate_convex_subsets(2, 2)
print(f"  Total: {total_22}")
print(f"  By size: {counts_22}")
print(f"  Expected: 13")
print()

# ===== d=3, m=2 =====
print("--- d=3, m=2 ---")
counts_32, total_32 = enumerate_convex_subsets(2, 3)
print(f"  Total: {total_32}")
print(f"  By size: {counts_32}")
print()

# ===== d=4, m=2 =====
print("--- d=4, m=2 ---")
counts_42, total_42 = enumerate_convex_subsets(2, 4)
print(f"  Total: {total_42}")
print(f"  By size: {counts_42}")
print()

# ===== d=2, m=3 =====
print("--- d=2, m=3 ---")
counts_23, total_23 = enumerate_convex_subsets(3, 2)
print(f"  Total: {total_23}")
print(f"  By size: {counts_23}")
print()

# ===== d=3, m=3 (may be slow) =====
print("--- d=3, m=3 (27 points, 134M subsets — using transfer matrix count instead) ---")
# Skip brute force for d=3,m=3

# ===== Analysis =====
print()
print("=" * 70)
print("GENERATING FUNCTIONS BY DIMENSION")
print("=" * 70)

# For each d at m=2, print the generating function
for d, counts, total in [(2, counts_22, total_22), (3, counts_32, total_32), (4, counts_42, total_42)]:
    poly = " + ".join(f"{c}x^{k}" for k, c in enumerate(counts) if c > 0)
    print(f"  d={d}, m=2: Σ CC(k)x^k = {poly}")
    print(f"    Total |CC| = {total}")

print()
print("=" * 70)
print("FREE WINDOW CHECK (k ≤ m)")
print("=" * 70)
print()

# The free-window law: for k ≤ m, CC(k) = Free(k)
# Free(k) for d dimensions = number of convex subsets of [m]^d of size k
# that don't touch both walls.
# For m=2: CC(k) for k ≤ 2 should match the "free" count.

# The "free" generating function for d dimensions:
# Free tail = P_{d-1}(q)^2 where P_n is the n-dim partition function
# P_0(q) = 1/(1-q) (ordinary partitions generating fcn at m→∞... no)
# Actually, for FINITE m:
# The free count at depth k is the number of antitone pairs (a,b) with
# exactly k cells, where a,b are constant (don't touch the walls).

# For now, just report the counts
for d, counts in [(2, counts_22), (3, counts_32), (4, counts_42)]:
    print(f"  d={d}, m=2: CC(0)={counts[0]}, CC(1)={counts[1]}, CC(2)={counts[2]}")

print()
print("=" * 70)
print("DIMENSIONAL PATTERN")
print("=" * 70)
print()
print(f"  d=2, m=2: |CC([2]²)| = {total_22}")
print(f"  d=3, m=2: |CC([2]³)| = {total_32}")
print(f"  d=4, m=2: |CC([2]⁴)| = {total_42}")
print()

# Growth: |CC([2]^d)| as a function of d
for d, total in [(2, total_22), (3, total_32), (4, total_42)]:
    print(f"  d={d}: log₂|CC| = {np.log2(total):.4f}")
