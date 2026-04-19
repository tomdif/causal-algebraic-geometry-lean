"""
MCMC sampler for convex subsets of [m]³ and exact counter for small m.

Element-level MCMC: add/remove one element, with local convexity checking.
Convexity check: after toggling element x, verify that no convexity
violation is created in the local neighborhood.
"""

import numpy as np
import time
from collections import defaultdict


class ConvexMCMC3D:
    """Element-level MCMC for convex subsets of [m]³."""

    def __init__(self, m, rng=None):
        self.m = m
        self.rng = rng or np.random.default_rng()
        # Grid stored as 3D boolean array
        self.grid = np.ones((m, m, m), dtype=bool)  # start full

    def size(self):
        return int(np.sum(self.grid))

    def is_convex_after_remove(self, x, y, z):
        """Check if removing (x,y,z) preserves convexity.

        Removing (x,y,z) violates convexity iff there exist
        (a,b,c) ≤ (x,y,z) ≤ (d,e,f) both in S.
        """
        m = self.m
        g = self.grid
        # Check: is (x,y,z) "between" two other elements?
        # Need: exists (a,b,c) ∈ S with a≤x, b≤y, c≤z
        # AND exists (d,e,f) ∈ S with d≥x, e≥y, f≥z
        has_below = False
        has_above = False

        # Check below: any element ≤ (x,y,z) still in S?
        for a in range(x + 1):
            if has_below:
                break
            for b in range(y + 1):
                if has_below:
                    break
                for c in range(z + 1):
                    if (a, b, c) != (x, y, z) and g[a, b, c]:
                        has_below = True
                        break

        if not has_below:
            return True  # (x,y,z) is minimal, removing is safe

        # Check above: any element ≥ (x,y,z) still in S?
        for a in range(x, m):
            if has_above:
                break
            for b in range(y, m):
                if has_above:
                    break
                for c in range(z, m):
                    if (a, b, c) != (x, y, z) and g[a, b, c]:
                        has_above = True
                        break

        if not has_above:
            return True  # (x,y,z) is maximal, removing is safe

        # Has both below and above: removing creates a "hole"
        # which violates convexity
        return False

    def is_convex_after_add(self, x, y, z):
        """Check if adding (x,y,z) preserves convexity.

        Adding (x,y,z) violates convexity iff there exist
        (a,b,c), (d,e,f) ∈ S with (a,b,c) ≤ (x,y,z) ≤ (d,e,f)
        but some element between (a,b,c) and (d,e,f) is NOT in S∪{(x,y,z)}.

        Equivalently: for all (a,b,c) ∈ S with a≤x,b≤y,c≤z:
          all elements between (a,b,c) and (x,y,z) must be in S.
        AND for all (d,e,f) ∈ S with d≥x,e≥y,f≥z:
          all elements between (x,y,z) and (d,e,f) must be in S.
        """
        m = self.m
        g = self.grid

        # Check: all elements in the "lower shadow" of (x,y,z) that are
        # connected to existing elements must be present
        # For each (a,b,c) ∈ S with a≤x, b≤y, c≤z:
        #   rectangle [a,x] × [b,y] × [c,z] must be entirely in S ∪ {(x,y,z)}
        for a in range(x + 1):
            for b in range(y + 1):
                for c in range(z + 1):
                    if not g[a, b, c]:
                        continue
                    # Check rectangle [a,x] × [b,y] × [c,z]
                    for i in range(a, x + 1):
                        for j in range(b, y + 1):
                            for k in range(c, z + 1):
                                if (i, j, k) != (x, y, z) and not g[i, j, k]:
                                    return False

        # For each (d,e,f) ∈ S with d≥x, e≥y, f≥z:
        #   rectangle [x,d] × [y,e] × [z,f] must be entirely in S ∪ {(x,y,z)}
        for d in range(x, m):
            for e in range(y, m):
                for f in range(z, m):
                    if not g[d, e, f]:
                        continue
                    for i in range(x, d + 1):
                        for j in range(y, e + 1):
                            for k in range(z, f + 1):
                                if (i, j, k) != (x, y, z) and not g[i, j, k]:
                                    return False
        return True

    def step(self):
        """One MCMC step: toggle a random element."""
        m = self.m
        x = self.rng.integers(m)
        y = self.rng.integers(m)
        z = self.rng.integers(m)

        if self.grid[x, y, z]:
            # Try to remove
            if self.is_convex_after_remove(x, y, z):
                self.grid[x, y, z] = False
                return True
        else:
            # Try to add
            if self.is_convex_after_add(x, y, z):
                self.grid[x, y, z] = True
                return True
        return False

    def randomize(self, n_steps=None):
        if n_steps is None:
            n_steps = self.m ** 3 * 500
        acc = 0
        for _ in range(n_steps):
            if self.step():
                acc += 1
        return acc / n_steps


if __name__ == '__main__':
    print("=== d=3 Monte Carlo ===")
    print()

    # Test for small m
    for m in [3, 4, 5, 6, 8, 10]:
        mc = ConvexMCMC3D(m)
        t0 = time.time()
        acc = mc.randomize(m ** 3 * 200)

        # Sample
        sizes = []
        n_samples = 5000
        thin = max(1, m ** 2)
        for _ in range(n_samples):
            for _ in range(thin):
                mc.step()
            sizes.append(mc.size())

        dt = time.time() - t0
        sizes = np.array(sizes)
        fill = np.mean(sizes) / m ** 3

        print(f"m={m:2d}: accept={acc:.3f}, <|S|>={np.mean(sizes):.1f}/{m**3}, "
              f"fill={fill:.3f}, std={np.std(sizes):.1f} ({dt:.1f}s)")

    print()
    print("=== Growth rate estimation ===")
    # For each m, estimate log Z(m) ≈ log|CC([m]³)| via thermodynamic integration
    # or flat histogram method. For now, just report fill fractions.
    # The fill fraction <|S|>/m³ should converge to a constant (the density
    # at the peak of the entropy).
