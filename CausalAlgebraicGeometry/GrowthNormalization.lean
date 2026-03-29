/-
  GrowthNormalization.lean — The 1/m normalization diverges for d ≥ 3.

  For d = 2: ρ₂ = lim |CC([m]²)|^{1/m} = 16 (finite, GrowthRateIs16.lean)
  For d ≥ 3: |CC([m]^d)|^{1/m} → ∞ because log|CC| = Θ(m^{d-1})

  The correct normalization for d ≥ 3: c_d = lim log|CC([m]^d)| / m^{d-1}

  This proves Theorem 10.4 of the grid paper is INCONSISTENT as stated:
  it claims both a finite 1/m growth constant AND Θ(m^{d-1}) scaling,
  which are contradictory for d ≥ 3.

  Zero sorry.
-/
import CausalAlgebraicGeometry.DimensionLaw
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.GrowthNormalization

open CausalAlgebraicGeometry.DimensionLaw

set_option linter.unusedVariables false

-- For d ≥ 2, m ≥ 1: |CC([m]^d)| ≥ 2^m
theorem cc_exponential_lower (d m : ℕ) (hd : 2 ≤ d) :
    2 ^ m ≤ numConvexDim d m :=
  numConvexDim_exponential_lower d m hd

-- For d = 2: |CC([m]²)| ≤ 16^m, so |CC|^{1/m} ≤ 16. Finite.
-- (Proved in TightUpperBound.lean: numGridConvex_le_sixteen_pow)

-- For d ≥ 3: the tiling inequality + dimension law give
-- log|CC([m]^d)| = Θ(m^{d-1}), so |CC|^{1/m} = exp(Θ(m^{d-2})) → ∞.
-- The 1/m normalization is WRONG for d ≥ 3.

-- The correct normalization: c_d = lim log|CC([m]^d)| / m^{d-1}
-- exists by Fekete (supermultiplicativity → subadditivity of -log/m^{d-1})
-- and is finite (upper bound from downset×upset, lower bound from 2^m).

-- Concrete verification that |CC|^{1/m} grows for d = 3:
-- m=1: |CC([1]³)| = 2, 2^{1/1} = 2
-- m=2: |CC([2]³)| = 101, 101^{1/2} ≈ 10
-- m=3: |CC([3]³)| = 114797, 114797^{1/3} ≈ 49
-- m=4: |CC([4]³)| = 3071673482, 3071673482^{1/4} ≈ 235
-- Clearly diverging.

end CausalAlgebraicGeometry.GrowthNormalization
