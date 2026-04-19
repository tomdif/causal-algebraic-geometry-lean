/-
  GrowthConstantStatus.lean — What's known about c_d = growth rate of |CC([m]^d)|.

  STATUS OF THE SANDWICH BOUNDS:

  Proved (SlabBijection.lean): L_d ≤ c_d ≤ 2 L_d
  where L_d = lim log(#downsets of [m]^d)/m^{d-1}.

  Proved (GrowthRateIs16.lean, independently): c_2 = log 16.
  Since L_2 = log 4 (from #downsets([m]²) = C(2m,m) ~ 4^m), this means c_2 = 2 L_2.
  The upper bound of the sandwich is TIGHT for d=2 (via an independent Catalan argument).

  Unproven for d ≥ 3: whether c_d = 2 L_d (upper bound tight).

  For d=3 specifically:
    L_3 = (9/2) ln 3 - 6 ln 2 ≈ 0.7849 (MacMahon box asymptotic for PP(m,m,m))
    2 L_3 ≈ 1.5697
    c_3 ∈ [0.7849, 1.5697] (sandwich)

    Numerical data from verified values:
      |CC([2]³)| = 101: log/4 = 1.154
      |CC([3]³)| = 114,797: log/9 = 1.295
    Ratio log|CC|/log(PP): 1.54 (m=2), 1.69 (m=3) — trending toward 2 slowly.

    These are consistent with c_3 = 2 L_3 but don't prove it.

  Lean theorem stating what's proved:
-/
import CausalAlgebraicGeometry.SlabBijection

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CausalAlgebraicGeometry.GrowthConstantStatus

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.DownsetSymmetry
open CausalAlgebraicGeometry.SlabBijection

noncomputable section
open scoped Classical

/-- **SANDWICH THEOREM**: log(downsets) ≤ log(convex) ≤ 2·log(downsets).

    This is the rigorously proved statement. The equality c_d = 2 L_d is
    NOT proved in general (only sandwich bounds). -/
theorem growth_sandwich (d m : ℕ) :
    Real.log (downsetCountDim d m : ℝ) ≤ Real.log (numConvexDim d m : ℝ) ∧
    Real.log (numConvexDim d m : ℝ) ≤ 2 * Real.log (downsetCountDim d m : ℝ) :=
  log_sandwich d m

/-- The sandwich gives bounds on the growth rate as a function of m. -/
theorem growth_bounds_d3 (m : ℕ) :
    Real.log (downsetCountDim 3 m : ℝ) ≤ Real.log (numConvexDim 3 m : ℝ) ∧
    Real.log (numConvexDim 3 m : ℝ) ≤ 2 * Real.log (downsetCountDim 3 m : ℝ) :=
  log_sandwich 3 m

/-- **STATUS STATEMENT (as a prose theorem via `True`)**:

    For d=3, the growth constant c_3 = lim log|CC([m]³)|/m²:
    - LOWER BOUND: c_3 ≥ L_3 where L_3 = lim log(downsetCount)/m² (proved).
    - UPPER BOUND: c_3 ≤ 2 L_3 (proved).
    - EQUALITY c_3 = 2 L_3: NOT PROVED for d=3. Was claimed in older framework
      documents; this claim is RETRACTED as of the April 19, 2026 audit.
    - For d=2, c_2 = 2 L_2 = log 16 is proved via GrowthRateIs16.lean (which uses
      an independent Catalan argument, not the sandwich). -/
theorem c3_status : True := trivial

end -- noncomputable section

end CausalAlgebraicGeometry.GrowthConstantStatus
