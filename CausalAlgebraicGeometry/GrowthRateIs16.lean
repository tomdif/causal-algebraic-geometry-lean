/-
  GrowthRateIs16.lean — The growth constant ρ for |CC([m]²)| equals 16.

  Main theorem: growth_constant_eq_neg_log_sixteen
    The Fekete limit of -log(numGridConvex n n) / n equals -log 16.

  Equivalently: lim_{n→∞} numGridConvex(n,n)^{1/n} = 16.

  Proof structure:
  Upper bound: a(n) ≤ 16^n gives the limit ≥ -log 16 direction (PROVED).
  Lower bound: a(n) ≥ C(2n,n)²/(2(n+1)) ≥ 16^n/poly(n) gives the ≤ direction.
    The squeeze argument requires:
    (a) C(2n,n) ≥ 4^n/(2n) [from Mathlib: four_pow_le_two_mul_self_mul_centralBinom]
    (b) The catalan lower bound [from RhoEquals16, fully proved via CrossingBound.lean]
    (c) log(poly(n))/n → 0 [standard real analysis]

  Status: Zero sorry. Zero custom axioms (only propext, Classical.choice, Quot.sound,
  Lean.ofReduceBool, Lean.trustCompiler from native_decide).
-/
import CausalAlgebraicGeometry.GrowthRateHelper

namespace CausalAlgebraicGeometry.GrowthRateIs16

open CausalAlgebraicGeometry.TightUpperBound
open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GrowthConstant
open CausalAlgebraicGeometry.RhoEquals16
open CausalAlgebraicGeometry.GrowthRateHelper
open Real Filter Topology

/-! ## Upper bound direction: Fekete limit ≥ -log 16 (PROVED) -/

/-- From numGridConvex m m ≤ 16^m, we get -log(a(m))/m ≥ -log 16 for all m ≥ 1. -/
theorem neg_log_div_ge (m : ℕ) (hm : m ≠ 0) :
    -Real.log 16 ≤ -Real.log (numGridConvex m m : ℝ) / m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have ha_pos : (0 : ℝ) < numGridConvex m m := Nat.cast_pos.mpr (numGridConvex_pos m m)
  have hle : (numGridConvex m m : ℝ) ≤ 16 ^ m := by exact_mod_cast numGridConvex_le_sixteen_pow m
  have hlog : Real.log (numGridConvex m m : ℝ) ≤ ↑m * Real.log 16 := by
    calc Real.log ↑(numGridConvex m m)
        ≤ Real.log ((16 : ℝ) ^ m) := Real.log_le_log ha_pos hle
      _ = ↑m * Real.log 16 := by rw [Real.log_pow]
  show -Real.log 16 ≤ -Real.log ↑(numGridConvex m m) / ↑m
  rw [neg_div, neg_le_neg_iff]
  rw [mul_comm] at hlog
  exact div_le_of_le_mul₀ (le_of_lt hm') (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)) hlog

/-- The Fekete limit is ≥ -log 16 (PROVED, sorry-free). -/
theorem fekete_limit_ge_neg_log_sixteen :
    -Real.log 16 ≤ neg_log_subadditive.lim := by
  have h_lim := neg_log_subadditive.tendsto_lim bddBelow_neg_log_div
  apply ge_of_tendsto h_lim
  filter_upwards [Filter.Ici_mem_atTop 1] with n hn
  exact neg_log_div_ge n (show n ≠ 0 from by
    intro h; subst h; exact absurd hn (by simp [Set.mem_Ici]))

/-! ## Lower bound direction: Fekete limit ≤ -log 16

The proof requires the asymptotic squeeze:
  -log(a(n))/n ≤ -log(C(2n,n)²/(2(n+1)))/n → -log 16

Key ingredients:
  - C(2n,n) ≥ 4^n/(2n) from Mathlib's four_pow_le_two_mul_self_mul_centralBinom
  - numGridConvex_ge_catalan_bound: a(n) ≥ C(2n,n)²/(2(n+1))
  - log(poly(n))/n → 0 for polynomial poly

These give: -log(16) ≤ -log(a(n))/n ≤ -log(16) + (2·log(2n) + log(2(n+1)))/n
and the correction → 0.
-/

/-- Central binomial lower bound: 4^n ≤ 2n · C(2n,n) for n ≥ 1.
    Reformulation of Mathlib's four_pow_le_two_mul_self_mul_centralBinom. -/
theorem choose_central_ge_div (n : ℕ) (hn : 0 < n) :
    4 ^ n ≤ 2 * n * Nat.choose (2 * n) n := by
  have h := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  rwa [Nat.centralBinom_eq_two_mul_choose] at h

/-- 16^n ≤ 4n² · C(2n,n)², from squaring the central binomial lower bound. -/
theorem sixteen_pow_le_sq (n : ℕ) (hn : 0 < n) :
    16 ^ n ≤ (2 * n) ^ 2 * Nat.choose (2 * n) n ^ 2 := by
  calc 16 ^ n = (4 ^ n) ^ 2 := by
          rw [← pow_mul, show n * 2 = 2 * n from by ring,
              show (4 : ℕ) ^ (2 * n) = (4 ^ 2) ^ n from pow_mul 4 2 n]; norm_num
    _ ≤ (2 * n * Nat.choose (2 * n) n) ^ 2 := Nat.pow_le_pow_left (choose_central_ge_div n hn) 2
    _ = (2 * n) ^ 2 * Nat.choose (2 * n) n ^ 2 := by ring

/-- The Fekete limit is ≤ -log 16.

    Proof sketch: From a(n) ≥ C(2n,n)²/(2(n+1)) and C(2n,n) ≥ 4^n/(2n):
    log(a(n))/n ≥ 2·log(4) - O(log(n)/n) = log(16) - o(1)
    So -log(a(n))/n ≤ -log(16) + o(1).
    Since the Fekete limit exists, L ≤ -log(16). -/
theorem fekete_limit_le_neg_log_sixteen :
    neg_log_subadditive.lim ≤ -Real.log 16 := by
  -- f(n) = -log(a(n))/n → L, g(n) = -log(16) + correction(n)/n → -log(16)
  -- f(n) ≤ g(n) for n ≥ 1 (from neg_log_div_le), so L ≤ -log(16).
  have h_lim := neg_log_subadditive.tendsto_lim bddBelow_neg_log_div
  -- The upper bound sequence g(n) → -log(16)
  have h_upper : Tendsto
      (fun n : ℕ => -Real.log 16 + (Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log 2) / ↑n)
      atTop (nhds (-Real.log 16)) := by
    have h := correction_tendsto_zero
    have : Tendsto (fun n : ℕ => -Real.log 16 +
        (Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log 2) / ↑n)
        atTop (nhds (-Real.log 16 + 0)) :=
      Filter.Tendsto.add tendsto_const_nhds h
    simp only [add_zero] at this
    exact this
  -- Apply le_of_tendsto_of_tendsto: f → L, g → -log(16), f ≤ g eventually, so L ≤ -log(16)
  exact le_of_tendsto_of_tendsto h_lim h_upper (eventually_atTop.mpr ⟨1, fun n hn =>
    neg_log_div_le n hn⟩)

/-! ## The main theorem -/

/-- The growth constant for |CC([m]²)| is exactly 16.
    The Fekete limit of -log(numGridConvex n n)/n equals -log 16.

    Equivalently: ρ = lim_{n→∞} numGridConvex(n,n)^{1/n} = 16. -/
theorem growth_constant_eq_neg_log_sixteen :
    neg_log_subadditive.lim = -Real.log 16 :=
  le_antisymm fekete_limit_le_neg_log_sixteen fekete_limit_ge_neg_log_sixteen

/-- Equivalent formulation: log(numGridConvex n n)/n → log 16. -/
theorem log_numGridConvex_div_tendsto_log_sixteen :
    Tendsto (fun n => Real.log (numGridConvex n n : ℝ) / ↑n) atTop (nhds (Real.log 16)) := by
  have h := neg_log_subadditive.tendsto_lim bddBelow_neg_log_div
  rw [growth_constant_eq_neg_log_sixteen] at h
  have h2 := h.neg
  simp only [neg_div, neg_neg] at h2
  exact h2

end CausalAlgebraicGeometry.GrowthRateIs16
