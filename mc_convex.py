"""
Monte Carlo and exact counting for convex subsets of [m]^d.

Uses transfer matrix method: enumerate convex subsets row by row,
where each row's "column configuration" is a contiguous interval
[l, u] ⊆ {0,...,m-1} (or empty). Two consecutive configurations
(c₁, c₂) are compatible iff their union doesn't violate convexity.

For d=2: transfer matrix on column configs, size O(m²).
For d=3: transfer matrix on 2D slice configs, size exponential in m.
         Use MCMC instead.
"""

import numpy as np
from scipy import sparse
import time


def column_configs(m):
    """All possible column configurations for a single row of [m]².
    Each config is a contiguous interval [l, u] or EMPTY.
    Returns list of (l, u) tuples; EMPTY = (m, -1).
    """
    configs = [(m, -1)]  # empty
    for l in range(m):
        for u in range(l, m):
            configs.append((l, u))
    return configs


def compatible_2d(c1, c2, m):
    """Check if column config c2 can follow c1 in a convex subset of [m]².

    Two rows with configs c1 = [l1, u1] and c2 = [l2, u2] are compatible iff
    the rectangle they span doesn't violate convexity.

    Key constraint: if row i has (a, j1) and row i+1 has (b, j2),
    and a ≤ b, then all (c, j) with a ≤ c ≤ b and min(j1,j2) ≤ j ≤ max(j1,j2)
    must be in S. For adjacent rows (b = a+1), this means the column ranges
    must be "nested" or "non-overlapping in a compatible way".

    Actually: for componentwise order, (i1, j1) ≤ (i2, j2) iff i1≤i2 AND j1≤j2.
    For rows i and i+1: element (i, j1) ≤ (i+1, j2) iff j1 ≤ j2.
    Convexity between these: all (i, j) and (i+1, j) for j1 ≤ j ≤ j2 must be in S.
    So: if row i contains column j1 and row i+1 contains column j2 ≥ j1,
    then row i must contain [j1, j2] and row i+1 must contain [j1, j2].
    """
    l1, u1 = c1
    l2, u2 = c2

    # Both empty: OK
    if l1 > u1 and l2 > u2:
        return True
    # One empty: OK (no comparability)
    if l1 > u1 or l2 > u2:
        return True

    # Both nonempty: [l1, u1] and [l2, u2]
    # For each j1 in [l1, u1] and j2 in [l2, u2] with j1 ≤ j2:
    # row i must contain [j1, j2] and row i+1 must contain [j1, j2].
    # Equivalently: [min(l1,l2), max(u1,u2)] ⊆ [l1,u1] ∩ [l2,u2]... no.
    # Let me think again.
    #
    # If j1 ∈ [l1,u1] and j2 ∈ [l2,u2] with j1 ≤ j2:
    # All (i, j) for j1 ≤ j ≤ j2 must be in row i → [j1,j2] ⊆ [l1,u1]
    # All (i+1, j) for j1 ≤ j ≤ j2 must be in row i+1 → [j1,j2] ⊆ [l2,u2]
    #
    # Taking j1 = l1 (leftmost in row i): need [l1, j2] ⊆ [l1,u1] for all
    # j2 ∈ [l2,u2] with j2 ≥ l1. So j2 ≤ u1. This means u2 ≤ u1 OR l2 > u1.
    # Wait, we need [l1, j2] ⊆ [l2, u2] too! So l2 ≤ l1.
    #
    # Taking j2 = u2 (rightmost in row i+1): need [j1, u2] ⊆ [l1,u1] for all
    # j1 ∈ [l1,u1] with j1 ≤ u2. So l1 ≤ u2 implies [l1,u2] ⊆ [l1,u1],
    # meaning u2 ≤ u1.
    # Also [l1, u2] ⊆ [l2, u2] means l2 ≤ l1.
    #
    # So if the intervals OVERLAP (l1 ≤ u2 and l2 ≤ u1), we need:
    # l2 ≤ l1 and u2 ≤ u1 (row i+1's interval is contained in row i's).
    # NO WAIT: we also need l1 ≤ u2. If l2 ≤ l1 and u2 ≤ u1, and they overlap
    # (l1 ≤ u2), then l2 ≤ l1 ≤ u2 ≤ u1. So [l2,u2] ⊆ [l1,u1]... no.
    # l2 ≤ l1 ≤ u2 ≤ u1 means [l1, u2] is the overlap.
    # Row i has [l1, u1] and row i+1 has [l2, u2] = [l2, u2].
    #
    # Hmm, I derived l2 ≤ l1 and u2 ≤ u1. That means row i+1 is CONTAINED
    # in row i? No: l2 ≤ l1 means row i+1 extends further LEFT than row i.
    # And u2 ≤ u1 means row i+1 is shorter on the RIGHT.
    # So row i+1 can stick out to the left but must be trimmed on the right.
    # That's the antitone-L (L shrinks), antitone-U (U shrinks) pattern.

    # If intervals DON'T overlap (l1 > u2 or l2 > u1):
    # If l1 > u2: row i is entirely to the right of row i+1.
    #   No j1 ∈ [l1,u1] has j1 ≤ j2 for any j2 ∈ [l2,u2].
    #   So no convexity constraint. Compatible! ✓
    # If l2 > u1: row i+1 is entirely to the right of row i.
    #   j1 ∈ [l1,u1], j2 ∈ [l2,u2], j1 ≤ j2: need [j1,j2] ⊆ [l1,u1]
    #   but j2 ≥ l2 > u1, so j2 > u1. Need j2 ≤ u1. Contradiction.
    #   So NO j1, j2 with j1 ≤ j2 can have [j1,j2] ⊆ [l1,u1]... wait.
    #   Actually the constraint is: j1 ∈ [l1,u1] and j2 ∈ [l2,u2] with j1 ≤ j2.
    #   If l2 > u1: j2 ≥ l2 > u1 ≥ j1. So j1 ≤ j2 always.
    #   Need all (i,j) for j1 ≤ j ≤ j2 in row i: [j1,j2] ⊆ [l1,u1].
    #   But j2 > u1, so j2 ∉ [l1,u1]. Violation!
    #   Unless j1 = j2 (impossible since j1 ≤ u1 < l2 ≤ j2).
    #   So: l2 > u1 is INCOMPATIBLE (unless one row is empty).

    # WAIT: that means row i+1 can't be strictly to the RIGHT of row i?
    # Let me verify: {(0,0), (1,1)} — is this convex?
    # (0,0) ≤ (1,1): 0≤1, 0≤1 → yes. Need all (i,j) with 0≤i≤1, 0≤j≤1.
    # That's (0,0), (0,1), (1,0), (1,1). Missing (0,1) and (1,0). NOT convex. ✓

    # And {(0,1), (1,0)} — is this convex?
    # (0,1) and (1,0): 0≤1 but 1>0. Incomparable. No constraint. CONVEX. ✓
    # Here l1=1, u1=1, l2=0, u2=0. l2=0 < l1=1 and u2=0 < u1=1.
    # Non-overlapping (l1=1 > u2=0). My rule says: l1 > u2 → compatible. ✓

    # So the rule is:
    # Both nonempty:
    #   If l1 > u2: compatible (row i entirely right of row i+1, incomparable)
    #   If l2 > u1: INCOMPATIBLE (would create unfilled rectangle)
    #   If they overlap (l1 ≤ u2 and l2 ≤ u1): need l2 ≤ l1 and u2 ≤ u1
    #     (which is equivalent to: the overlap is [l1, u2], and both intervals
    #     contain it, which means the overlap IS [l1, u2] ⊆ [l1,u1] ∩ [l2,u2])
    #     Actually l2 ≤ l1 and u2 ≤ u1 just means U is non-increasing and
    #     L is non-increasing (the antitone property, going from row i to i+1).

    # Wait, I have l2 ≤ l1 (L DECREASES from row to row) and u2 ≤ u1
    # (U DECREASES from row to row). Both boundaries shrink.
    # This means row i+1 is "inside" row i in terms of the right boundary
    # but "outside" on the left. That's the staircase shape.

    # Let me just implement the check directly.
    overlap = (l1 <= u2) and (l2 <= u1)
    if not overlap:
        # No overlap: compatible iff row i+1 is to the LEFT of row i
        # (l1 > u2), not to the right (l2 > u1)
        if l2 > u1:
            return False
        return True

    # Overlap: need l2 ≤ l1 and u2 ≤ u1
    return l2 <= l1 and u2 <= u1


def transfer_matrix_2d(m):
    """Build the transfer matrix for convex subsets of [m]²."""
    configs = column_configs(m)
    n = len(configs)
    T = np.zeros((n, n), dtype=np.int64)
    for i, c1 in enumerate(configs):
        for j, c2 in enumerate(configs):
            if compatible_2d(c1, c2, m):
                T[i, j] = 1
    return T, configs


def exact_count_2d(m):
    """Exact count |CC([m]²)| using transfer matrix."""
    T, configs = transfer_matrix_2d(m)
    n = len(configs)

    # Start vector: any config for row 0
    v = np.ones(n, dtype=np.int64)

    # Multiply T^{m-1} times to propagate through all rows
    for _ in range(m - 1):
        v = T.T @ v  # T.T because we want T[c1,c2] * v[c1] summed over c1

    # Total = sum of all entries of v
    return int(np.sum(v))


def exact_count_2d_brute(m):
    """Brute force count for verification."""
    grid = [(i, j) for i in range(m) for j in range(m)]
    n = len(grid)
    count = 0
    for mask in range(1 << n):
        S = set()
        for idx in range(n):
            if mask & (1 << idx):
                S.add(grid[idx])
        convex = True
        for a in S:
            if not convex: break
            for b in S:
                if not convex: break
                if a[0] <= b[0] and a[1] <= b[1]:
                    for c in grid:
                        if a[0] <= c[0] <= b[0] and a[1] <= c[1] <= b[1]:
                            if c not in S:
                                convex = False
                                break
        if convex:
            count += 1
    return count


if __name__ == '__main__':
    print("=== Convex Subset Counter (Transfer Matrix) ===")
    print()

    # Verify against brute force
    print("Verification (d=2):")
    for m in range(2, 6):
        t0 = time.time()
        tm_count = exact_count_2d(m)
        dt_tm = time.time() - t0
        bf_count = exact_count_2d_brute(m)
        match = "✓" if tm_count == bf_count else f"✗ (TM={tm_count})"
        print(f"  |CC([{m}]²)| = {bf_count} {match}  ({dt_tm:.4f}s)")

    print()

    # Compute for larger m
    print("Growth rate estimation (d=2):")
    prev = None
    for m in range(2, 30):
        t0 = time.time()
        c = exact_count_2d(m)
        dt = time.time() - t0
        rho = c ** (1.0 / m)
        ratio = c / prev if prev else 0
        print(f"  m={m:2d}: |CC|={c:>25d}  ρ_m={rho:8.4f}  "
              f"ratio={ratio:10.4f}  ({dt:.3f}s)")
        prev = c
        if dt > 30:
            print("  (stopping, too slow)")
            break

    print()
    print(f"  ρ₂ = 16 (proved)")
