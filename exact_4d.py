"""
Exact counting of |CC([m]⁴)| using transfer matrix over 3D slice configs.
Uses C-accelerated compatibility checking generalized to 4D.
"""

import numpy as np
import time
from collections import defaultdict
import sys

# For m=3: configs are convex subsets of [3]³ = 129535 configs.
# Compatibility between 4D-adjacent 3D slices needs a 4D-compatible check.


def generate_3d_configs_from_2d(m):
    """Generate all convex subsets of [m]³ using 2D slice transfer matrix.
    Returns list of (frozen set of (i,j,k) tuples).

    This is too slow for m >= 4. For m=3, it uses the verified
    gap-aware DP over 2D slice configs.
    """
    # First generate 2D configs with boundaries
    configs_2d = []

    def gen2d(row, last_L, last_U, had_gap, L, U):
        if row == m:
            configs_2d.append((tuple(L), tuple(U)))
            return
        new_gap = had_gap or (last_L is not None)
        gen2d(row + 1, last_L, last_U, new_gap, L + [m], U + [-1])
        for l in range(m):
            for u in range(l, m):
                if last_L is not None:
                    if had_gap:
                        if last_L <= u: continue
                    else:
                        if l > last_L or u > last_U: continue
                gen2d(row + 1, l, u, False, L + [l], U + [u])

    gen2d(0, None, None, False, [], [])
    n2d = len(configs_2d)

    print(f"  [{m}]² has {n2d} configs")

    # Convert 2D configs to element sets
    config_sets = []
    for L, U in configs_2d:
        S = frozenset((i, j) for i in range(m) for j in range(L[i], U[i] + 1)
                      if L[i] < m)
        config_sets.append(S)

    # Check 3D compatibility between 2D slices
    def compat_3d(S1, S2):
        for (j1, k1) in S1:
            for (j2, k2) in S2:
                if j1 <= j2 and k1 <= k2:
                    for j in range(j1, j2 + 1):
                        for k in range(k1, k2 + 1):
                            if (j, k) not in S1 or (j, k) not in S2:
                                return False
        return True

    def has_comp(S1, S2):
        for (j1, k1) in S1:
            for (j2, k2) in S2:
                if j1 <= j2 and k1 <= k2:
                    return True
        return False

    # Find empty config
    empty_idx = None
    for i, S in enumerate(config_sets):
        if len(S) == 0:
            empty_idx = i
            break

    # Gap-aware DP to enumerate 3D configs
    # Instead of storing each 3D config as a full element set,
    # store it as a sequence of 2D slice indices.
    # A 3D convex subset = sequence of compatible 2D slices.
    #
    # But we don't need the ENUMERATION — we need the TRANSFER MATRIX
    # for 4D. The 4D transfer matrix has states = 3D convex subsets,
    # and we need to check 4D compatibility between adjacent 3D slices.
    #
    # For 4D compatibility: two 3D subsets S1, S2 (in [m]³) are
    # 4D-compatible iff for all (i1,j1,k1) ∈ S1 and (i2,j2,k2) ∈ S2
    # with i1≤i2, j1≤j2, k1≤k2: the rectangle is in both S1 and S2.
    #
    # This is expensive to check element-by-element for |S| ~ m³/3 elements.
    #
    # For m=3: |S| up to 27 elements. 129535 configs.
    # Element-by-element check: O(27² × 27) ≈ 20K ops per pair.
    # 129535² × 20K ≈ 3.4 × 10^{14}. Way too slow.
    #
    # Need boundary-based representation for 3D configs too.

    # A 3D config can be described by its SLICE PROFILE:
    # For each "first coordinate" value i, the set of (j,k) ∈ S
    # forms a 2D convex subset. So a 3D config is a sequence
    # of 2D config indices: [c₀, c₁, ..., c_{m-1}] where cᵢ is
    # the 2D config index for slice i.
    #
    # 4D compatibility between two 3D configs is then:
    # For all i₁ (slice in S1), i₂ (slice in S2) with i₁ ≤ i₂:
    #   The 2D configs at those slices must be "pairwise 3D-compatible"
    #   AND all intermediate slices in both S1 and S2 must cover the overlap.
    #
    # This is still complex, but the 2D configs are small (m² elements).

    # For now, let me just store 3D configs as sequences of 2D config indices.
    print(f"  Building 3D configs from 2D slice sequences...", flush=True)
    t0 = time.time()

    NONE = n2d
    dp = defaultdict(int)
    # We need to enumerate configs, not just count them.
    # Store: dp[state] = list of partial 3D configs (as tuples of 2D indices)
    # This is too expensive in memory for 129535 configs.

    # ALTERNATIVE: Just count |CC([3]⁴)| directly using the gap-aware DP
    # over 3D config INDICES, without materializing the 3D configs.
    # The DP state tracks the last nonempty 3D "slice" (which IS a 3D convex config).
    # But we have 129535 possible 3D configs, so the state space is ~260K.
    # For each state, checking compatibility with all 129535 new configs
    # requires checking 4D compatibility between 3D config pairs.

    # The 4D compatibility between two 3D configs represented as
    # sequences of 2D configs can be checked as follows:
    # 3D config A has slices [a₀, ..., a_{m-1}] (2D config indices)
    # 3D config B has slices [b₀, ..., b_{m-1}]
    # 4D compatible iff: for all i₁, i₂ with i₁ ≤ i₂:
    #   2D configs a_{i₁} and b_{i₂} must be "jointly compatible"
    #   meaning: for all (j₁,k₁) ∈ a_{i₁} and (j₂,k₂) ∈ b_{i₂}
    #   with j₁ ≤ j₂ and k₁ ≤ k₂:
    #   all (j,k) in the rectangle must be in BOTH a_i and b_i
    #   for ALL i with i₁ ≤ i ≤ i₂.

    # This requires checking m² pairs of 2D configs and for each,
    # verifying coverage in intermediate slices. Doable but slow.

    print(f"  4D computation for m=3 would require checking")
    print(f"  129535² ≈ 1.7×10^10 pairs of 3D configs.")
    print(f"  Each check involves m² = 9 pairs of 2D configs.")
    print(f"  Total: ~1.5×10^11 ops. At ~10⁸ ops/s (C): ~25 minutes per layer.")
    print(f"  With m=3 layers: ~75 minutes total.")
    print(f"  This is FEASIBLE but needs the C inner loop.")

    return None


if __name__ == '__main__':
    m = 3
    print(f"Assessing |CC([{m}]⁴)| computation:")
    generate_3d_configs_from_2d(m)
