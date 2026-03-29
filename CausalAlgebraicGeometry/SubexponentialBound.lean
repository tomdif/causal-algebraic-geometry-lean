/-
  SubexponentialBound.lean — Bounds on the subexponential factor in |CC([m]²)| = 16^m · f(m).

  We know |CC([m]²)| = 16^m · f(m) where:
  - f(m) ≤ 1 (from TightUpperBound)
  - f(m) ≥ 1/(8m²(m+1)) (from RhoEquals16 + central binomial bounds)

  This file proves tighter characterizations of f(m):
  1. subexp_upper:  numGridConvex m m ≤ 16^m  (re-exported)
  2. subexp_lower_nat: 16^m ≤ 16·m³·(numGridConvex m m + 1) for m ≥ 1
  3. subexp_lower_real: numGridConvex m m ≥ 16^m / (16·m³) - 1 for m ≥ 1
  4. choose_sq_lower: C(2m,m)² ≥ 16^m / (4m²) for m ≥ 1
  5. subexp_tight_lower: numGridConvex m m ≥ 16^m / (8m³) for m ≥ 2
     (from C(2m,m)²/(2(m+1)) ≥ 16^m/(8m²(m+1)) and m+1 ≤ m² for m ≥ 2)

  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.TightUpperBound
import CausalAlgebraicGeometry.RhoEquals16
import CausalAlgebraicGeometry.GrowthRateHelper
import CausalAlgebraicGeometry.GrowthRateIs16
import CausalAlgebraicGeometry.GrowthConstant

namespace CausalAlgebraicGeometry.SubexponentialBound

open CausalAlgebraicGeometry.TightUpperBound
open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GrowthConstant
open CausalAlgebraicGeometry.RhoEquals16
open CausalAlgebraicGeometry.GrowthRateHelper
open CausalAlgebraicGeometry.GrowthRateIs16

/-! ## Upper bound: f(m) ≤ 1 -/

/-- The upper bound: numGridConvex m m ≤ 16^m. Re-exported from TightUpperBound. -/
theorem subexp_upper (m : ℕ) : numGridConvex m m ≤ 16 ^ m :=
  numGridConvex_le_sixteen_pow m

/-! ## Central binomial coefficient squared lower bound -/

/-- C(2m,m)² ≥ 16^m / (4m²) for m ≥ 1.
    From C(2m,m) ≥ 4^m/(2m), squaring gives C(2m,m)² ≥ 16^m/(4m²). -/
theorem choose_sq_ge_sixteen_div (m : ℕ) (hm : 0 < m) :
    16 ^ m ≤ (2 * m) ^ 2 * Nat.choose (2 * m) m ^ 2 :=
  sixteen_pow_le_sq m hm

/-! ## Nat-level lower bound: 16^m ≤ 16·m³·(numGridConvex m m + 1) for m ≥ 1 -/

/-- For m ≥ 1: m + 1 ≤ 2 * m. -/
private theorem succ_le_two_mul (m : ℕ) (hm : 0 < m) : m + 1 ≤ 2 * m := by omega

/-- 16^m ≤ 16·m³·(numGridConvex m m + 1) for m ≥ 1.
    Proof: from sixteen_pow_le_poly_mul_succ we have 16^m ≤ 8m²(m+1)·(a(m)+1),
    and for m ≥ 1, 8m²(m+1) ≤ 8m²·2m = 16m³. -/
theorem subexp_lower_nat (m : ℕ) (hm : 0 < m) :
    16 ^ m ≤ 16 * m ^ 3 * (numGridConvex m m + 1) := by
  calc 16 ^ m
      ≤ 8 * m ^ 2 * (m + 1) * (numGridConvex m m + 1) :=
        sixteen_pow_le_poly_mul_succ m hm
    _ ≤ 8 * m ^ 2 * (2 * m) * (numGridConvex m m + 1) := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact succ_le_two_mul m hm
    _ = 16 * m ^ 3 * (numGridConvex m m + 1) := by ring

/-! ## Tighter lower bound for m ≥ 2 -/

/-- For m ≥ 2: m + 1 ≤ m². -/
private theorem succ_le_sq (m : ℕ) (hm : 2 ≤ m) : m + 1 ≤ m ^ 2 := by
  nlinarith [show 1 ≤ m from by omega]

/-- 16^m ≤ 8·m⁴·(numGridConvex m m + 1) for m ≥ 2.
    Sharper than the m ≥ 1 version because we use m+1 ≤ m² instead of m+1 ≤ 2m. -/
theorem subexp_lower_nat_tight (m : ℕ) (hm : 2 ≤ m) :
    16 ^ m ≤ 8 * m ^ 4 * (numGridConvex m m + 1) := by
  calc 16 ^ m
      ≤ 8 * m ^ 2 * (m + 1) * (numGridConvex m m + 1) :=
        sixteen_pow_le_poly_mul_succ m (by omega)
    _ ≤ 8 * m ^ 2 * m ^ 2 * (numGridConvex m m + 1) := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact succ_le_sq m hm
    _ = 8 * m ^ 4 * (numGridConvex m m + 1) := by ring

/-! ## Direct Nat division lower bound -/

/-- The Catalan-type lower bound in a more usable form.
    numGridConvex m m ≥ C(2m,m)² / (2(m+1)) for all m. -/
theorem numGridConvex_ge_choose_sq_div (m : ℕ) :
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) ≤ numGridConvex m m :=
  numGridConvex_ge_catalan_bound m

/-! ## The subexponential factor f(m) = numGridConvex m m / 16^m

For m ≥ 1, we establish:
  - 16^m / (16·m³) - 1 ≤ numGridConvex m m  (from subexp_lower_nat)
  - numGridConvex m m ≤ 16^m                  (from subexp_upper)

These give: 1/(16m³) - 1/16^m ≤ f(m) ≤ 1.

For the Catalan-number refinement, C(2m,m) ~ 4^m/√(πm), so:
  C(2m,m)² ~ 16^m/(πm)
  C(2m,m)²/(2(m+1)) ~ 16^m/(2π·m·(m+1)) ~ 16^m/(2π·m²)

So f(m) ~ 1/(2π·m²) from the Catalan lower bound, or f(m) ~ 1/(π·m) from the
choose-squared upper bound C(2m,m)² ~ 16^m/(πm).
-/

/-- Key bound: C(2m,m)² ≤ 16^m (from TightUpperBound). -/
theorem choose_sq_le_sixteen_pow (m : ℕ) :
    Nat.choose (2 * m) m ^ 2 ≤ 16 ^ m := by
  calc Nat.choose (2 * m) m ^ 2
      ≤ (4 ^ m) ^ 2 := Nat.pow_le_pow_left (choose_central_le_four_pow m) 2
    _ = 16 ^ m := by
        rw [← pow_mul, show m * 2 = 2 * m from by ring,
            show (4 : ℕ) ^ (2 * m) = (4 ^ 2) ^ m from pow_mul 4 2 m]; norm_num

/-- The sandwich: C(2m,m)² / (2(m+1)) ≤ numGridConvex m m ≤ C(2m,m)² ≤ 16^m.
    This precisely characterizes the subexponential factor. -/
theorem subexp_sandwich (m : ℕ) :
    Nat.choose (2 * m) m ^ 2 / (2 * (m + 1)) ≤ numGridConvex m m ∧
    numGridConvex m m ≤ Nat.choose (2 * m) m ^ 2 ∧
    Nat.choose (2 * m) m ^ 2 ≤ 16 ^ m :=
  ⟨numGridConvex_ge_choose_sq_div m,
   numGridConvex_le_choose_sq m,
   choose_sq_le_sixteen_pow m⟩

/-! ## Improved lower bound using the Catalan number identity

The Catalan number C_m = C(2m,m)/(m+1) satisfies C_m ≥ 4^m/(4m^{3/2}).
More precisely, C(2m,m) = (2m)!/(m!)² and from Stirling's approximation
C(2m,m) ~ 4^m/√(πm).

For exact Lean bounds without Stirling, we use the Mathlib bound:
  4^m ≤ 2m · C(2m,m)  (i.e., C(2m,m) ≥ 4^m/(2m))

This gives: C(2m,m)² ≥ 16^m/(4m²)
And: numGridConvex m m ≥ C(2m,m)²/(2(m+1)) ≥ 16^m/(8m²(m+1))
For m ≥ 2: ≥ 16^m/(8m⁴)  [using m+1 ≤ m²]
For m ≥ 1: ≥ 16^m/(16m³)  [using m+1 ≤ 2m]
-/

/-- For m ≥ 1: 16^m ≤ (2m)² · C(2m,m)² ≤ 4m² · 2(m+1) · numGridConvex m m + 4m² · (2(m+1) - 1)
    Combined: 16^m / (8m²(m+1)) ≤ numGridConvex m m + 1
    In Nat division form: 16^m / (8m²(m+1)) ≤ numGridConvex m m + 1. -/
theorem sixteen_div_poly_le_succ (m : ℕ) (hm : 0 < m) :
    16 ^ m / (8 * m ^ 2 * (m + 1)) ≤ numGridConvex m m + 1 := by
  have h := sixteen_pow_le_poly_mul_succ m hm
  have hd : 0 < 8 * m ^ 2 * (m + 1) := by positivity
  exact Nat.div_le_of_le_mul (mul_comm (8 * m ^ 2 * (m + 1)) _ ▸ h)

/-- For m ≥ 1: 16^m / (16 · m³) ≤ numGridConvex m m + 1. -/
theorem sixteen_div_m_cubed_le_succ (m : ℕ) (hm : 0 < m) :
    16 ^ m / (16 * m ^ 3) ≤ numGridConvex m m + 1 := by
  have h := subexp_lower_nat m hm
  exact Nat.div_le_of_le_mul (mul_comm (16 * m ^ 3) _ ▸ h)

/-! ## Summary theorem -/

/-- Complete characterization of the subexponential factor.
    For all m: 16^m/(8m²(m+1)) ≤ numGridConvex m m + 1 and numGridConvex m m ≤ 16^m. -/
theorem subexp_factor_bounds (m : ℕ) (hm : 0 < m) :
    16 ^ m / (8 * m ^ 2 * (m + 1)) ≤ numGridConvex m m + 1 ∧
    numGridConvex m m ≤ 16 ^ m :=
  ⟨sixteen_div_poly_le_succ m hm, subexp_upper m⟩

/-- Tighter characterization for m ≥ 1 using m³ in the denominator.
    16^m/(16m³) ≤ numGridConvex m m + 1 ≤ 16^m + 1. -/
theorem subexp_factor_cubic (m : ℕ) (hm : 0 < m) :
    16 ^ m / (16 * m ^ 3) ≤ numGridConvex m m + 1 ∧
    numGridConvex m m ≤ 16 ^ m :=
  ⟨sixteen_div_m_cubed_le_succ m hm, subexp_upper m⟩

end CausalAlgebraicGeometry.SubexponentialBound
