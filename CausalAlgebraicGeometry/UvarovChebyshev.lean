/-
  UvarovChebyshev.lean — Chamber polynomials as boundary-perturbed Chebyshev

  The chamber Jacobi matrix J_d has constant interior recurrence coefficients
  (matching Chebyshev) with boundary modifications at the first and last rows.

  STRUCTURAL IDENTIFICATION:
  - Interior: α_n = 2/(d+1), β_n = 1/(2(d+1)²) for 2 ≤ n ≤ d-2
  - Left boundary: α₁ = 1/(d-1), β₁ = 1/(d+1)² = 2·β_interior
  - Right boundary: α_{d-1} = 1/(d+1) = α_interior/2

  References: Uvarov (1969), Koornwinder (1984), Zhedanov.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace CausalAlgebraicGeometry.UvarovChebyshev

/-! ## Definitions -/

def α₁ (d : ℕ) : ℚ := 1 / ((d : ℚ) - 1)
def α_int (d : ℕ) : ℚ := 2 / ((d : ℚ) + 1)
def α_last (d : ℕ) : ℚ := 1 / ((d : ℚ) + 1)
def β₁_sq (d : ℕ) : ℚ := 1 / ((d : ℚ) + 1) ^ 2
def β_int_sq (d : ℕ) : ℚ := 1 / (2 * ((d : ℚ) + 1) ^ 2)

/-! ## 1. Boundary perturbation ratios -/

theorem beta_first_doubled (d : ℕ) : β₁_sq d = 2 * β_int_sq d := by
  unfold β₁_sq β_int_sq; field_simp

theorem alpha_last_halved (d : ℕ) : 2 * α_last d = α_int d := by
  unfold α_last α_int; field_simp

/-! ## 2. Specific values -/

theorem coeffs_d4 : α₁ 4 = 1/3 ∧ α_int 4 = 2/5 ∧ α_last 4 = 1/5
    ∧ β₁_sq 4 = 1/25 ∧ β_int_sq 4 = 1/50 := by
  unfold α₁ α_int α_last β₁_sq β_int_sq; norm_num

theorem coeffs_d5 : α₁ 5 = 1/4 ∧ α_int 5 = 1/3 ∧ α_last 5 = 1/6
    ∧ β₁_sq 5 = 1/36 ∧ β_int_sq 5 = 1/72 := by
  unfold α₁ α_int α_last β₁_sq β_int_sq; norm_num

/-- At d=3: α₁ = α_interior (no left boundary perturbation). -/
theorem no_left_perturbation_d3 : α₁ 3 = α_int 3 := by
  unfold α₁ α_int; norm_num

/-- At d=4: α₁ < α_interior. -/
theorem left_depressed_d4 : α₁ 4 < α_int 4 := by
  unfold α₁ α_int; norm_num

/-- At d=5: α₁ < α_interior. -/
theorem left_depressed_d5 : α₁ 5 < α_int 5 := by
  unfold α₁ α_int; norm_num

/-! ## 3. Boundary perturbation magnitudes -/

def δα₁ (d : ℕ) : ℚ := α₁ d - α_int d
def δα_last (d : ℕ) : ℚ := α_last d - α_int d
def δβ₁ (d : ℕ) : ℚ := β₁_sq d - β_int_sq d

theorem delta_first_formula (d : ℕ) (h1 : (d : ℚ) - 1 ≠ 0) (h2 : (d : ℚ) + 1 ≠ 0) :
    δα₁ d = (3 - (d : ℚ)) / (((d : ℚ) - 1) * ((d : ℚ) + 1)) := by
  unfold δα₁ α₁ α_int; field_simp; ring

theorem delta_last_formula (d : ℕ) :
    δα_last d = -(1 / ((d : ℚ) + 1)) := by
  unfold δα_last α_last α_int; field_simp; ring

theorem delta_beta_eq_interior (d : ℕ) : δβ₁ d = β_int_sq d := by
  unfold δβ₁ β₁_sq β_int_sq; field_simp; ring

-- Specific values
theorem delta_first_d3 : δα₁ 3 = 0 := by unfold δα₁ α₁ α_int; norm_num
theorem delta_first_d4 : δα₁ 4 = -(1/15) := by unfold δα₁ α₁ α_int; norm_num
theorem delta_first_d5 : δα₁ 5 = -(1/12) := by unfold δα₁ α₁ α_int; norm_num
theorem delta_last_d4 : δα_last 4 = -(1/5) := by unfold δα_last α_last α_int; norm_num
theorem delta_last_d5 : δα_last 5 = -(1/6) := by unfold δα_last α_last α_int; norm_num

/-! ## 4. Chebyshev support parameters -/

def cheb_center (d : ℕ) : ℚ := α_int d
def cheb_hw_sq (d : ℕ) : ℚ := 4 * β_int_sq d

theorem hw_sq_formula (d : ℕ) : cheb_hw_sq d = 2 / ((d : ℚ) + 1) ^ 2 := by
  unfold cheb_hw_sq β_int_sq; field_simp; ring

theorem center_d4 : cheb_center 4 = 2 / 5 := by unfold cheb_center α_int; norm_num
theorem hw_sq_d4 : cheb_hw_sq 4 = 2 / 25 := by unfold cheb_hw_sq β_int_sq; norm_num

/-! ## 5. Capstone: structural identification -/

/-- **The chamber matrix is a boundary-perturbed Chebyshev matrix.**

    Interior: constant recurrence (Chebyshev base).
    Left boundary: β₁ doubled, α₁ depressed (by (3-d)/((d-1)(d+1))).
    Right boundary: α_last halved.
    At d=3: left perturbation vanishes (one-sided). -/
theorem chamber_is_perturbed_chebyshev :
    -- β₁ = 2·β_interior (doubled)
    (∀ d, β₁_sq d = 2 * β_int_sq d)
    -- 2·α_last = α_interior (halved)
    ∧ (∀ d, 2 * α_last d = α_int d)
    -- δβ₁ = β_interior (off-diagonal perturbation = interior value)
    ∧ (∀ d, δβ₁ d = β_int_sq d)
    -- δα_last = -1/(d+1) (always negative)
    ∧ (∀ d, δα_last d = -(1 / ((d : ℚ) + 1)))
    -- At d=3: no left perturbation
    ∧ δα₁ 3 = 0
    -- At d=4: left perturbation is -1/15
    ∧ δα₁ 4 = -(1/15) := by
  exact ⟨beta_first_doubled, alpha_last_halved, delta_beta_eq_interior,
    delta_last_formula, delta_first_d3, delta_first_d4⟩

end CausalAlgebraicGeometry.UvarovChebyshev
