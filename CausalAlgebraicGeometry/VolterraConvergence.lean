/-
  VolterraConvergence.lean — Explicit error bound for the Volterra SV ratio

  THE RESULT:
  The SV ratio σ₁/σ₂ = 3 - 4sin²(θ) where θ = π/(4m+2).
  The error from 3 is exactly 4sin²(θ), which satisfies:
    0 ≤ 4sin²(θ) ≤ 4θ²

  Since θ = π/(4m+2), the error is bounded by 4π²/(4m+2)².
  For m ≥ 1: 4m+2 ≥ 6, so error ≤ 4π²/36 = π²/9 < 1.1.

  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.VolterraGap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace CausalAlgebraicGeometry.VolterraConvergence

open Real VolterraGap

/-! ## The error is nonneg (ratio ≤ 3) -/

/-- The error 4sin²(θ) is nonnegative. -/
theorem error_nonneg (m : ℕ) (_hm : 1 ≤ m) :
    let θ := π / (4 * ↑m + 2)
    0 ≤ 4 * sin θ ^ 2 := by
  intro θ
  positivity

/-- Combining with sv_ratio_error_bound: the ratio approaches 3 from below. -/
theorem ratio_between_zero_and_three (m : ℕ) (hm : 1 ≤ m) :
    let θ := π / (4 * ↑m + 2)
    0 < sin (3 * θ) / sin θ ∧ sin (3 * θ) / sin θ ≤ 3 :=
  ⟨sv_ratio_pos m hm, sv_ratio_le_three m hm⟩

/-! ## The sin²(θ) ≤ θ² bound -/

/-- sin²(θ) ≤ θ² for all θ. Follows from |sin θ| ≤ |θ|. -/
theorem sin_sq_le_sq (θ : ℝ) : sin θ ^ 2 ≤ θ ^ 2 :=
  Real.sin_sq_le_sq

/-- **The explicit error bound**: 3 - ratio ≤ 4θ². -/
theorem error_le_four_theta_sq (m : ℕ) (hm : 1 ≤ m) :
    let θ := π / (4 * ↑m + 2)
    3 - sin (3 * θ) / sin θ ≤ 4 * θ ^ 2 := by
  intro θ
  rw [sv_ratio_error_bound m hm]
  have := sin_sq_le_sq θ
  linarith

/-! ## Explicit numerical bound -/

/-- θ = π/(4m+2): for m ≥ 1, 4m+2 ≥ 6, so θ ≤ π/6. -/
theorem theta_bound (m : ℕ) (hm : 1 ≤ m) :
    let θ := π / (4 * ↑m + 2)
    θ ≤ π / 6 := by
  intro θ
  have hm_cast : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h6 : (0 : ℝ) < 6 := by norm_num
  have hden : (0 : ℝ) < 4 * ↑m + 2 := by positivity
  rw [div_le_div_iff₀ hden h6]
  nlinarith [pi_pos]

/-- The error bound in terms of m: 3 - ratio ≤ 4(π/(4m+2))². -/
theorem error_bound_in_m (m : ℕ) (hm : 1 ≤ m) :
    let θ := π / (4 * ↑m + 2)
    3 - sin (3 * θ) / sin θ ≤ 4 * (π / (4 * ↑m + 2)) ^ 2 :=
  error_le_four_theta_sq m hm

/-! ## Convergence rate -/

/-- θ is strictly decreasing in m. -/
theorem theta_decreasing (m1 m2 : ℕ) (_hm1 : 1 ≤ m1) (h : m1 < m2) :
    π / (4 * ↑m2 + 2) < π / (4 * ↑m1 + 2) := by
  have h1 : (0 : ℝ) < 4 * ↑m1 + 2 := by positivity
  have h2 : (0 : ℝ) < 4 * ↑m2 + 2 := by positivity
  rw [div_lt_div_iff₀ h2 h1]
  have : (m1 : ℝ) < (m2 : ℝ) := by exact_mod_cast h
  nlinarith [pi_pos]

/-- **Summary of convergence properties.** -/
theorem volterra_convergence_summary (m : ℕ) (hm : 1 ≤ m) :
    let θ := π / (4 * ↑m + 2)
    -- The ratio is in (0, 3]
    (0 < sin (3 * θ) / sin θ)
    ∧ (sin (3 * θ) / sin θ ≤ 3)
    -- The error is exactly 4sin²(θ)
    ∧ (3 - sin (3 * θ) / sin θ = 4 * sin θ ^ 2)
    -- The error is bounded by 4θ²
    ∧ (3 - sin (3 * θ) / sin θ ≤ 4 * θ ^ 2) :=
  ⟨sv_ratio_pos m hm, sv_ratio_le_three m hm,
   sv_ratio_error_bound m hm, error_le_four_theta_sq m hm⟩

end CausalAlgebraicGeometry.VolterraConvergence
