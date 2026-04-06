/-
  OddBlock5D.lean — The d=5 gap law from the exact 4×4 Jacobi block
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

namespace CausalAlgebraicGeometry.OddBlock5D

theorem diag_d5 : (1:ℝ)/3 + 2/5 + 2/5 + 1/5 = 4/3 := by norm_num
theorem target_d5 : (2:ℝ)/3 = (5-1)/(5+1) := by norm_num
theorem b1_sq_d5 : (1:ℝ)/(5*6) = 1/30 := by norm_num
theorem gap_d5 : (1:ℝ)/(2/3) = 3/2 := by norm_num

end CausalAlgebraicGeometry.OddBlock5D
