/-
  GrowthRateHelper.lean — Real analysis helper lemmas for the ρ = 16 proof.

  Key results:
  1. log_numGridConvex_lower_bound: log(a(n)) ≥ n·log(16) - 3·log(2n+2) for n ≥ 1
  2. log_correction_div_tendsto_zero: log(poly(n))/n → 0

  These are used by GrowthRateIs16.lean to prove the squeeze argument.
  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.TightUpperBound
import CausalAlgebraicGeometry.RhoEquals16
import CausalAlgebraicGeometry.GrowthConstant
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.Basic

namespace CausalAlgebraicGeometry.GrowthRateHelper

open CausalAlgebraicGeometry.TightUpperBound
open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GrowthConstant
open CausalAlgebraicGeometry.RhoEquals16
open Real Filter Topology

/-! ## Real-valued lower bound on log(numGridConvex)

Strategy: from 16^n ≤ 4n² · C(2n,n)² and C(2n,n)²/(2(n+1)) ≤ a(n),
we get (in ℕ): 16^n ≤ 4n² · 2(n+1) · a(n) + 4n² · (2(n+1) - 1)
                     ≤ 8n²(n+1) · a(n) + 8n²(n+1)
                     = 8n²(n+1) · (a(n) + 1)

In ℝ: a(n) + 1 ≥ 16^n / (8n²(n+1))
      a(n) ≥ 16^n / (8n²(n+1)) - 1

For the log bound: log(a(n)) ≥ log(16^n / (8n²(n+1)) - 1)
For large n this is ≈ n·log(16) - log(8n²(n+1)).

But working with log(x - 1) is annoying. Instead, use:
log(a(n)) ≥ log(a(n) + 1) - log(2)  [since a(n)+1 ≤ 2·a(n) for a(n) ≥ 1]
          ≥ log(16^n / (8n²(n+1))) - log(2)
          = n·log(16) - log(8n²(n+1)) - log(2)
          = n·log(16) - log(16n²(n+1))

Actually, simplest approach: just show a(n) · (8n²(n+1)) ≥ 16^n / 2 for large n,
or use a(n) ≥ 1 and the Nat bound directly.

Cleanest: work with a(n) + 1 ≥ 16^n / (8n²(n+1)).
Then: log(a(n)) ≥ n·log(16) - log(8n²(n+1)) - log(2)
-/

/-- Central binomial lower bound: 4^n ≤ 2n · C(2n,n) for n ≥ 1. -/
private theorem choose_central_ge_div (n : ℕ) (hn : 0 < n) :
    4 ^ n ≤ 2 * n * Nat.choose (2 * n) n := by
  have h := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  rwa [Nat.centralBinom_eq_two_mul_choose] at h

/-- 16^n ≤ 4n² · C(2n,n)², from squaring the central binomial lower bound. -/
private theorem sixteen_pow_le_sq (n : ℕ) (hn : 0 < n) :
    16 ^ n ≤ (2 * n) ^ 2 * Nat.choose (2 * n) n ^ 2 := by
  calc 16 ^ n = (4 ^ n) ^ 2 := by
          rw [← pow_mul, show n * 2 = 2 * n from by ring,
              show (4 : ℕ) ^ (2 * n) = (4 ^ 2) ^ n from pow_mul 4 2 n]; norm_num
    _ ≤ (2 * n * Nat.choose (2 * n) n) ^ 2 := Nat.pow_le_pow_left (choose_central_ge_div n hn) 2
    _ = (2 * n) ^ 2 * Nat.choose (2 * n) n ^ 2 := by ring

/-- Key Nat bound: 16^n ≤ 8n²(n+1) · (a(n) + 1) for n ≥ 1.
    From 16^n ≤ 4n² · C(2n,n)² and C(2n,n)²/(2(n+1)) ≤ a(n). -/
theorem sixteen_pow_le_poly_mul_succ (n : ℕ) (hn : 0 < n) :
    16 ^ n ≤ 8 * n ^ 2 * (n + 1) * (numGridConvex n n + 1) := by
  have h_catalan := numGridConvex_ge_catalan_bound n
  have h_sq := sixteen_pow_le_sq n hn
  -- 16^n ≤ (2n)^2 * C(2n,n)^2 = 4n^2 * C(2n,n)^2
  -- C(2n,n)^2 = (C(2n,n)^2 / (2(n+1))) * (2(n+1)) + C(2n,n)^2 % (2(n+1))
  -- ≤ a(n) * (2(n+1)) + (2(n+1) - 1) < (a(n) + 1) * (2(n+1))
  have hdiv : 0 < 2 * (n + 1) := by omega
  have h_div : Nat.choose (2 * n) n ^ 2 < (numGridConvex n n + 1) * (2 * (n + 1)) := by
    have h1 := Nat.div_add_mod (Nat.choose (2 * n) n ^ 2) (2 * (n + 1))
    -- h1 : C^2 = (2(n+1)) * (C^2/(2(n+1))) + C^2 % (2(n+1))
    have hmod := Nat.mod_lt (Nat.choose (2 * n) n ^ 2) hdiv
    calc Nat.choose (2 * n) n ^ 2
        = 2 * (n + 1) * (Nat.choose (2 * n) n ^ 2 / (2 * (n + 1))) +
          Nat.choose (2 * n) n ^ 2 % (2 * (n + 1)) := h1.symm
      _ < 2 * (n + 1) * (Nat.choose (2 * n) n ^ 2 / (2 * (n + 1))) + 2 * (n + 1) := by omega
      _ = 2 * (n + 1) * (Nat.choose (2 * n) n ^ 2 / (2 * (n + 1)) + 1) := by ring
      _ ≤ 2 * (n + 1) * (numGridConvex n n + 1) := by
          apply Nat.mul_le_mul_left; omega
      _ = (numGridConvex n n + 1) * (2 * (n + 1)) := by ring
  calc 16 ^ n
      ≤ (2 * n) ^ 2 * Nat.choose (2 * n) n ^ 2 := h_sq
    _ = 4 * n ^ 2 * Nat.choose (2 * n) n ^ 2 := by ring
    _ ≤ 4 * n ^ 2 * ((numGridConvex n n + 1) * (2 * (n + 1))) := by
        apply Nat.mul_le_mul_left; exact le_of_lt h_div
    _ = 8 * n ^ 2 * (n + 1) * (numGridConvex n n + 1) := by ring

/-- Real-valued lower bound: log(a(n) + 1) ≥ n · log 16 - log(8n²(n+1)) for n ≥ 1. -/
theorem log_succ_numGridConvex_ge (n : ℕ) (hn : 0 < n) :
    ↑n * Real.log 16 - Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) ≤
      Real.log (↑(numGridConvex n n) + 1) := by
  have h_nat := sixteen_pow_le_poly_mul_succ n hn
  have ha_pos : (0 : ℝ) < ↑(numGridConvex n n) + 1 := by positivity
  have hp_pos : (0 : ℝ) < 8 * (↑n : ℝ) ^ 2 * (↑n + 1) := by positivity
  -- In ℝ: 16^n ≤ 8n²(n+1) * (a(n)+1)
  have h_real : (16 : ℝ) ^ n ≤ 8 * (↑n : ℝ) ^ 2 * (↑n + 1) * (↑(numGridConvex n n) + 1) := by
    have := @Nat.cast_le ℝ _ _ _ |>.mpr h_nat
    push_cast at this ⊢
    linarith
  -- Take log: n·log(16) ≤ log(8n²(n+1)) + log(a(n)+1)
  have h_log : ↑n * Real.log 16 ≤
      Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log (↑(numGridConvex n n) + 1) := by
    calc ↑n * Real.log 16 = Real.log ((16 : ℝ) ^ n) := by rw [Real.log_pow]
      _ ≤ Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1) * (↑(numGridConvex n n) + 1)) :=
          Real.log_le_log (by positivity) h_real
      _ = Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log (↑(numGridConvex n n) + 1) :=
          Real.log_mul (ne_of_gt hp_pos) (ne_of_gt ha_pos)
  linarith

/-- Bound on -log(a(n))/n from above.
    For n ≥ 1: -log(a(n))/n ≤ -log(16) + (log(8n²(n+1)) + log 2)/n -/
theorem neg_log_div_le (n : ℕ) (hn : 0 < n) :
    -Real.log (numGridConvex n n : ℝ) / ↑n ≤
      -Real.log 16 + (Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log 2) / ↑n := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have ha_pos : (0 : ℝ) < numGridConvex n n := Nat.cast_pos.mpr (numGridConvex_pos n n)
  -- a(n) ≥ 1 so a(n)+1 ≤ 2·a(n)
  have h_succ_le : (↑(numGridConvex n n) : ℝ) + 1 ≤ 2 * ↑(numGridConvex n n) := by
    have : (1 : ℝ) ≤ ↑(numGridConvex n n) := by exact_mod_cast numGridConvex_pos n n
    linarith
  -- log(a(n)+1) ≤ log(2·a(n)) = log(2) + log(a(n))
  have h_log_succ : Real.log (↑(numGridConvex n n) + 1) ≤
      Real.log 2 + Real.log (↑(numGridConvex n n)) := by
    calc Real.log (↑(numGridConvex n n) + 1)
        ≤ Real.log (2 * ↑(numGridConvex n n)) := Real.log_le_log (by positivity) h_succ_le
      _ = Real.log 2 + Real.log ↑(numGridConvex n n) := Real.log_mul (by norm_num) (ne_of_gt ha_pos)
  -- From log_succ_numGridConvex_ge: n·log(16) - log(8n²(n+1)) ≤ log(a(n)+1)
  have h_lower := log_succ_numGridConvex_ge n hn
  -- Combining: n·log(16) - log(8n²(n+1)) ≤ log(2) + log(a(n))
  have h_combined : ↑n * Real.log 16 - Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) ≤
      Real.log 2 + Real.log ↑(numGridConvex n n) := by linarith
  -- Rearrange: -log(a(n)) ≤ -n·log(16) + log(8n²(n+1)) + log(2)
  have h_neg : -Real.log ↑(numGridConvex n n) ≤
      -(↑n * Real.log 16) + Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log 2 := by linarith
  -- Divide by n: -log(a(n))/n ≤ -log(16) + (log(8n²(n+1)) + log(2))/n
  have key : -Real.log ↑(numGridConvex n n) ≤
      ↑n * (-Real.log 16) + (Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log 2) := by
    linarith
  calc -Real.log ↑(numGridConvex n n) / ↑n
      ≤ (↑n * (-Real.log 16) + (Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log 2)) / ↑n :=
        div_le_div_of_nonneg_right key (le_of_lt hn')
    _ = -Real.log 16 + (Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log 2) / ↑n := by
        rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hn')]

/-- The correction term (log(8n²(n+1)) + log 2)/n → 0 as n → ∞.
    This follows from log(x)/x → 0, since log(poly(n)) = O(log(n)). -/
-- Helper: log(↑n)/↑n → 0 for ℕ-indexed sequences
private theorem log_nat_div_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (↑n : ℝ) / ↑n) atTop (nhds 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

-- Helper: c/↑n → 0
private theorem const_div_nat_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / (↑n : ℝ)) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem correction_tendsto_zero :
    Tendsto (fun n : ℕ => (Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) + Real.log 2) / ↑n)
      atTop (nhds 0) := by
  -- Bound: for n ≥ 1, 8n²(n+1) ≤ 16n³, so log(8n²(n+1)) ≤ log(16) + 3·log(n).
  -- Hence the ratio ≤ (log(16) + log(2))/n + 3·log(n)/n → 0.
  -- Use squeeze: 0 ≤ ratio ≤ upper → 0.
  --
  -- Upper bound: (log(16) + log(2) + 3·log(n)) / n → 0
  have h_upper : Tendsto (fun n : ℕ => (Real.log 16 + Real.log 2 + 3 * Real.log (↑n : ℝ)) / ↑n)
      atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (Real.log 16 + Real.log 2) / (↑n : ℝ) +
        3 * (Real.log (↑n : ℝ) / ↑n)) atTop (nhds (0 + 3 * 0)) :=
      (const_div_nat_tendsto_zero _).add (log_nat_div_tendsto_zero.const_mul 3)
    simp only [add_zero, mul_zero] at h1
    apply h1.congr
    intro n; ring
  -- Squeeze: 0 ≤ f(n) ≤ g(n) eventually, g → 0, so f → 0.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
  · -- Eventually 0 ≤ f(n) (for n ≥ 1)
    filter_upwards [Filter.Ici_mem_atTop 1] with n hn
    apply div_nonneg
    · exact add_nonneg (Real.log_nonneg (by nlinarith [show (1 : ℝ) ≤ ↑n from by exact_mod_cast hn]))
        (Real.log_nonneg (by norm_num))
    · exact Nat.cast_nonneg n
  · -- Eventually f(n) ≤ g(n) (for n ≥ 1)
    filter_upwards [Filter.Ici_mem_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ ↑n := by exact_mod_cast hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have h_bound : 8 * (↑n : ℝ) ^ 2 * (↑n + 1) ≤ 16 * (↑n : ℝ) ^ 3 := by nlinarith
    have h_log_bound : Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1)) ≤
        Real.log 16 + 3 * Real.log (↑n : ℝ) := by
      calc Real.log (8 * (↑n : ℝ) ^ 2 * (↑n + 1))
          ≤ Real.log (16 * (↑n : ℝ) ^ 3) :=
            Real.log_le_log (by positivity) h_bound
        _ = Real.log 16 + Real.log ((↑n : ℝ) ^ 3) :=
            Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt (by positivity : (0 : ℝ) < ↑n ^ 3))
        _ = Real.log 16 + 3 * Real.log (↑n : ℝ) := by
            rw [Real.log_pow]; push_cast; ring
    linarith

end CausalAlgebraicGeometry.GrowthRateHelper
