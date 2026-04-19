"""
Wang-Landau estimation of log|CC([m]³)| for larger m.

Strategy: Instead of counting all convex subsets directly, use the
Wang-Landau algorithm to estimate the density of states g(n) where
n = |S| is the size of the convex subset.

Then log|CC([m]³)| = log(Σ_n g(n)).

The Wang-Landau algorithm modifies the sampling weight to achieve
a flat histogram over sizes, allowing exploration of all size ranges.

For growth rate: ρ₃ = lim |CC([m]³)|^{1/m²}.
"""

import numpy as np
import time
import sys


class FastConvexMCMC3D:
    """Optimized element-level MCMC for convex subsets of [m]³.

    Uses numpy arrays and vectorized checks for speed.
    """

    def __init__(self, m, rng=None):
        self.m = m
        self.rng = rng or np.random.default_rng(42)
        self.grid = np.ones((m, m, m), dtype=np.int8)
        self._size = m * m * m

    def size(self):
        return self._size

    def _can_remove(self, x, y, z):
        """Can (x,y,z) be removed while preserving convexity?

        (x,y,z) can be removed iff it's NOT strictly between two other
        elements of S. It's between a and b iff a ≤ (x,y,z) ≤ b.
        So check: exists a ∈ S below AND b ∈ S above (both ≠ (x,y,z)).
        """
        m = self.m
        g = self.grid

        # Quick check: is it on the boundary (minimal or maximal)?
        # If no element below or no element above, safe to remove.

        # Check below: any (a,b,c) with a≤x, b≤y, c≤z, (a,b,c)≠(x,y,z)?
        has_below = False
        for a in range(x + 1):
            if has_below: break
            for b in range(y + 1):
                if has_below: break
                for c in range(z + 1):
                    if (a != x or b != y or c != z) and g[a, b, c]:
                        has_below = True
                        break

        if not has_below:
            return True

        # Check above
        has_above = False
        for a in range(x, m):
            if has_above: break
            for b in range(y, m):
                if has_above: break
                for c in range(z, m):
                    if (a != x or b != y or c != z) and g[a, b, c]:
                        has_above = True
                        break

        return not has_above

    def _can_add(self, x, y, z):
        """Can (x,y,z) be added while preserving convexity?

        Adding (x,y,z) creates a violation iff there exist a ∈ S below (x,y,z)
        such that some element between a and (x,y,z) is NOT in S,
        OR there exist b ∈ S above (x,y,z) with a missing element between.
        """
        m = self.m
        g = self.grid

        # Check: for all a ∈ S with a ≤ (x,y,z):
        #   all elements in [a, (x,y,z)] must be in S ∪ {(x,y,z)}
        for a0 in range(x + 1):
            for a1 in range(y + 1):
                for a2 in range(z + 1):
                    if not g[a0, a1, a2]:
                        continue
                    # Check rectangle [a, (x,y,z)]
                    for i in range(a0, x + 1):
                        for j in range(a1, y + 1):
                            for k in range(a2, z + 1):
                                if i == x and j == y and k == z:
                                    continue
                                if not g[i, j, k]:
                                    return False

        # Check: for all b ∈ S with b ≥ (x,y,z):
        for b0 in range(x, m):
            for b1 in range(y, m):
                for b2 in range(z, m):
                    if not g[b0, b1, b2]:
                        continue
                    for i in range(x, b0 + 1):
                        for j in range(y, b1 + 1):
                            for k in range(z, b2 + 1):
                                if i == x and j == y and k == z:
                                    continue
                                if not g[i, j, k]:
                                    return False
        return True

    def step_wang_landau(self, log_g):
        """Wang-Landau step: propose toggle, accept with g(old)/g(new)."""
        m = self.m
        x = self.rng.integers(m)
        y = self.rng.integers(m)
        z = self.rng.integers(m)

        old_size = self._size

        if self.grid[x, y, z]:
            if not self._can_remove(x, y, z):
                return old_size, False
            new_size = old_size - 1
            log_accept = log_g[old_size] - log_g[new_size]
            if log_accept >= 0 or np.log(self.rng.random()) < log_accept:
                self.grid[x, y, z] = 0
                self._size = new_size
                return new_size, True
            return old_size, False
        else:
            if not self._can_add(x, y, z):
                return old_size, False
            new_size = old_size + 1
            log_accept = log_g[old_size] - log_g[new_size]
            if log_accept >= 0 or np.log(self.rng.random()) < log_accept:
                self.grid[x, y, z] = 1
                self._size = new_size
                return new_size, True
            return old_size, False


def wang_landau_3d(m, max_iterations=50, sweeps_per_check=None,
                   f_final=1.0 + 1e-8, flatness=0.6):
    """Wang-Landau algorithm for |CC([m]³)|.

    Returns log_g (log density of states) and log_Z (log partition function).
    """
    mc = FastConvexMCMC3D(m)
    n_max = m ** 3

    if sweeps_per_check is None:
        sweeps_per_check = max(10000, n_max * 100)

    log_g = np.zeros(n_max + 1)
    hist = np.zeros(n_max + 1, dtype=np.int64)
    ln_f = 1.0  # modification factor (in log space)

    iteration = 0
    total_steps = 0

    while ln_f > np.log(f_final) and iteration < max_iterations:
        # Run sweeps
        for _ in range(sweeps_per_check):
            size, accepted = mc.step_wang_landau(log_g)
            log_g[size] += ln_f
            hist[size] += 1
            total_steps += 1

        # Check flatness
        visited = hist[hist > 0]
        if len(visited) > 1:
            flat = np.min(visited) / np.mean(visited)
        else:
            flat = 0

        iteration += 1

        if flat > flatness or iteration % 5 == 0:
            if flat > flatness:
                ln_f /= 2
                hist[:] = 0

            # Report
            nonzero = np.where(hist > 0)[0]
            if len(nonzero) > 0:
                size_range = f"sizes {nonzero[0]}-{nonzero[-1]}"
            else:
                size_range = "no data"

            log_Z_est = np.log(np.sum(np.exp(log_g - np.max(log_g)))) + np.max(log_g)
            print(f"  iter={iteration:3d}, ln_f={ln_f:.6f}, flat={flat:.4f}, "
                  f"{size_range}, log_Z≈{log_Z_est:.2f}, "
                  f"steps={total_steps//1000}K")

    # Final estimate
    log_Z = np.log(np.sum(np.exp(log_g - np.max(log_g)))) + np.max(log_g)
    return log_g, log_Z


if __name__ == '__main__':
    print("=== Wang-Landau for |CC([m]³)| ===")
    print()

    # Validate against known exact values
    known = {2: 101, 3: 129535, 4: 4664028094}

    for m in [2, 3, 4, 5, 6, 7, 8]:
        print(f"m={m} (n_max={m**3}):")
        t0 = time.time()

        sweeps = max(50000, m**3 * 500)
        log_g, log_Z = wang_landau_3d(m, max_iterations=30,
                                       sweeps_per_check=sweeps,
                                       f_final=1.0001,
                                       flatness=0.5)

        dt = time.time() - t0

        if m in known:
            exact_logZ = np.log(known[m])
            print(f"  log|CC| = {log_Z:.4f} (exact: {exact_logZ:.4f}, "
                  f"ratio: {np.exp(log_Z - exact_logZ):.4f})")
        else:
            print(f"  log|CC| ≈ {log_Z:.4f}")

        rho_est = np.exp(log_Z / m**2)
        print(f"  ρ₃ estimate: |CC|^{{1/m²}} ≈ {rho_est:.4f}")
        print(f"  Time: {dt:.1f}s")
        print()

        if dt > 300:
            print("  (stopping, too slow)")
            break
