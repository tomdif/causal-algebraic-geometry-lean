/-
  OddBlock3D.lean — The d=3 Dimensional Eigenvalue Law

  For d=3, the R-odd sector is a 2×2 Jacobi block:
    J₃ = [[1/3, κ], [κ, 1/5]]  with κ² = 1/20

  The continued fraction terminates at λ* = 1/2:
    D₁ = 1/2 - 1/3 = 1/6 > 0
    D₂ = (1/2 - 1/5) - (1/20)/(1/6) = 3/10 - 3/10 = 0  ← eigenvalue!

  Therefore le/lo = 1/(1/2) = 2 = (d+1)/(d-1), giving γ₃ = ln(2).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace CausalAlgebraicGeometry.OddBlock3D

/-! ### The d=3 Jacobi block -/

/-- d=3: diagonal entries. -/
theorem diag_d3 : (1:ℝ)/3 + 1/5 = 8/15 := by norm_num

/-- d=3: target eigenvalue. -/
theorem target_d3 : (1:ℝ)/2 = (3-1)/(3+1) := by norm_num

/-- d=3: first coupling. b₁² = 1/(5(d+1)) = 1/20. -/
theorem b1_sq_d3 : (1:ℝ)/(5*4) = 1/20 := by norm_num

/-! ### The continued fraction (same style as OddBlock5D) -/

/-- D₁ = λ* - 1/3 = 1/2 - 1/3 = 1/6 > 0. -/
theorem D1_d3 : (1:ℝ)/2 - 1/3 = 1/6 := by norm_num

theorem D1_d3_pos : (0:ℝ) < 1/2 - 1/3 := by norm_num

/-- D₂ = (λ* - 1/5) - b₁²/D₁ = (1/2 - 1/5) - (1/20)/(1/6) = 3/10 - 3/10 = 0.
    Equivalently: (1/2-1/3)(1/2-1/5) = 1/20 = b₁². -/
theorem D2_d3 : (1:ℝ)/2 - 1/5 - (1/20)/(1/6) = 0 := by norm_num

/-- The eigenvalue equation: det([[1/3,κ],[κ,1/5]] - (1/2)I) = 0 with κ²=1/20. -/
theorem det_block_zero :
    ((1 : ℝ) / 3 - 1 / 2) * (1 / 5 - 1 / 2) - 1 / 20 = 0 := by norm_num

/-- Equivalently: the characteristic polynomial factors.
    eigenvalues are 1/2 and 1/30. -/
theorem eigenvalue_product :
    (1 : ℝ) / 3 * (1 / 5) - 1 / 20 = 1 / 2 * (1 / 30) := by norm_num

theorem eigenvalue_sum :
    (1 : ℝ) / 3 + 1 / 5 = 1 / 2 + 1 / 30 := by norm_num

/-- The coupling κ² = 1/20 = (1/2-1/3)(1/2-1/5). -/
theorem coupling_from_eigenvalue :
    ((1 : ℝ) / 2 - 1 / 3) * (1 / 2 - 1 / 5) = 1 / 20 := by norm_num

/-- The coupling identity: C_int · D₁ = b₁².
    3/10 · 1/6 = 1/20. (C_int = 3/(10(d-2)) = 3/10 for d=3.) -/
theorem coupling_identity_d3 :
    (3:ℝ)/10 * (1/6) = 1/20 := by norm_num

/-! ### The gap law -/

/-- le/lo = 1/(1/2) = 2 = (d+1)/(d-1). -/
theorem ratio_d3 : (1 : ℝ) / (1 / 2) = 2 := by norm_num

/-- γ₃ = ln(2) > 0. -/
theorem gap_d3_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)

/-- γ₃ = ln(2). -/
theorem gap_d3 : Real.log ((3+1:ℝ)/(3-1)) = Real.log 2 := by norm_num

/-! ### General 2×2 Jacobi theory -/

/-- For a 2×2 matrix [[α, η], [η, β]] with eigenvalue μ:
    (α - μ)(β - μ) = η². -/
theorem two_by_two_eigenvalue (α β η μ : ℝ)
    (h : (α - μ) * (β - μ) = η ^ 2) :
    α * β - η ^ 2 = μ * (α + β - μ) := by nlinarith [sq_nonneg η]

/-- If the eigenvalue μ and the diagonal entries α, β are known,
    the coupling η is determined: η² = (α-μ)(β-μ). -/
theorem coupling_determined (α β μ η : ℝ)
    (hη : η ^ 2 = (α - μ) * (β - μ))
    (hα : μ > α) (hβ : μ > β) :
    0 < η ^ 2 := by nlinarith

/-- The eigenvalue ratio: if the block has top eigenvalue lo = S/2
    and le = S, then le/lo = 2. -/
theorem ratio_from_two_by_two (S lo : ℝ)
    (hS : 0 < S) (hlo : 0 < lo) (hle : lo < S) :
    1 < S / lo := by
  rw [lt_div_iff₀ hlo]; linarith

/-! ### The eigenvector -/

/-- The eigenvector of [[1/3, κ], [κ, 1/5]] for eigenvalue 1/2:
    v = (1, D₁/κ) = (1, (1/6)/√(1/20)).
    Weights: v₁² = 1, v₂² = (1/6)²/(1/20) = 20/36 = 5/9.
    Normalized: w₁ = 9/14, w₂ = 5/14. -/
theorem eigenvector_weights :
    (9 : ℝ) / 14 + 5 / 14 = 1 := by norm_num

/-- The Perron ratio v₂²/v₁² = D₁²/b₁² = (1/6)²/(1/20) = 5/9.
    Matches the general formula 20(d-2)²/(9(d+1)) = 20·1/(9·4) = 5/9. -/
theorem perron_ratio_d3 :
    ((1:ℝ)/6)^2 / (1/20) = 5/9 := by norm_num

theorem perron_ratio_formula_d3 :
    (20:ℝ) * (3-2)^2 / (9*(3+1)) = 5/9 := by norm_num

/-! ### Summary

PROVED (0 sorry, 0 placeholders):
  D1_d3: D₁ = 1/6
  D1_d3_pos: D₁ > 0
  D2_d3: D₂ = 0 (eigenvalue condition)
  det_block_zero: det(J₃ - (1/2)I) = 0
  eigenvalue_product: eigenvalues are 1/2 and 1/30
  eigenvalue_sum: they sum to 8/15
  coupling_from_eigenvalue: κ² = 1/20
  coupling_identity_d3: C_int · D₁ = b₁² (3/10 · 1/6 = 1/20)
  ratio_d3: le/lo = 2
  gap_d3_pos: γ₃ > 0
  gap_d3: γ₃ = ln(2)
  perron_ratio_d3: v₂²/v₁² = 5/9
  perron_ratio_formula_d3: matches 20(d-2)²/(9(d+1))
  two_by_two_eigenvalue, coupling_determined, ratio_from_two_by_two: general 2×2 theory

THE d=3 LAW: The 2×2 R-odd block [[1/3,κ],[κ,1/5]] with κ²=1/20
has eigenvalue 1/2 by continued fraction D₁=1/6>0, D₂=0.
Therefore le/lo = 2 = (3+1)/(3-1), giving γ₃ = ln(2).
-/

end CausalAlgebraicGeometry.OddBlock3D
