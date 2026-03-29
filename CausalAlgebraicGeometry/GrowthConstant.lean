/-
  GrowthConstant.lean -- Existence of the growth constant ρ for |CC([m]²)|

  From the proved supermultiplicativity a(m+n) ≥ a(m) · a(n), we derive:

  1. numGridConvex_pos: a(m) ≥ 1 for all m
  2. log_superadditive: log(a(m)) is superadditive
  3. neg_log_subadditive: u(m) = -log(a(m)) is subadditive
  4. numGridConvex_pow_le: a(m)^k ≤ a(k·m)
  5. numGridConvex_le_exp: a(m) ≤ 32^m (from MonotoneProfileBound)
  6. bddBelow_neg_log_div: BddBelow (-log(a(n))/n) (from 5)
  7. growth_constant_exists: Fekete's lemma gives convergence.

  Zero sorry. Zero custom axioms.
  The BddBelow hypothesis has been PROVED (not assumed) via the exponential bound.
-/
import CausalAlgebraicGeometry.Supermultiplicativity
import CausalAlgebraicGeometry.MonotoneProfileBound
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CausalAlgebraicGeometry.GrowthConstant

open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GridClassification
open CausalAlgebraicGeometry.MonotoneProfileBound
open Real Filter Topology

/-! ## Positivity of numGridConvex -/

theorem empty_isGridConvex (m n : ℕ) : IsGridConvex m n ∅ := by
  intro a ha; simp at ha

theorem numGridConvex_pos (m n : ℕ) : 0 < numGridConvex m n := by
  unfold numGridConvex
  apply Finset.card_pos.mpr
  exact ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, empty_isGridConvex m n⟩⟩

/-! ## Superadditivity of log counts -/

theorem log_superadditive (m n : ℕ) :
    Real.log (numGridConvex m m) + Real.log (numGridConvex n n) ≤
      Real.log (numGridConvex (m + n) (m + n)) := by
  have hm : (0 : ℝ) < numGridConvex m m := Nat.cast_pos.mpr (numGridConvex_pos m m)
  have hn : (0 : ℝ) < numGridConvex n n := Nat.cast_pos.mpr (numGridConvex_pos n n)
  rw [← Real.log_mul (ne_of_gt hm) (ne_of_gt hn)]
  apply Real.log_le_log (mul_pos hm hn)
  exact_mod_cast supermultiplicativity m n

theorem neg_log_subadditive :
    Subadditive (fun m => -Real.log (numGridConvex m m : ℝ)) := by
  intro m n; linarith [log_superadditive m n]

/-! ## Iterated supermultiplicativity -/

theorem numGridConvex_pow_le (m : ℕ) (k : ℕ) :
    (numGridConvex m m) ^ k ≤ numGridConvex (k * m) (k * m) := by
  induction k with
  | zero => simp only [Nat.zero_mul, pow_zero]; exact numGridConvex_pos 0 0
  | succ k ih =>
    rw [pow_succ]
    calc _ ≤ numGridConvex (k * m) (k * m) * numGridConvex m m :=
          Nat.mul_le_mul_right _ ih
      _ ≤ numGridConvex (k * m + m) (k * m + m) := supermultiplicativity (k * m) m
      _ = numGridConvex ((k + 1) * m) ((k + 1) * m) := by ring_nf

theorem log_numGridConvex_mul_le (m k : ℕ) :
    k * Real.log (numGridConvex m m) ≤ Real.log (numGridConvex (k * m) (k * m)) := by
  have hm : (0 : ℝ) < numGridConvex m m := Nat.cast_pos.mpr (numGridConvex_pos m m)
  rw [← Real.log_pow]
  apply Real.log_le_log (pow_pos hm k)
  exact_mod_cast numGridConvex_pow_le m k

/-! ## BddBelow from the exponential bound -/

theorem bddBelow_neg_log_div :
    BddBelow (Set.range (fun n => -Real.log (numGridConvex n n : ℝ) / n)) := by
  use -Real.log 32
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  by_cases hn : n = 0
  · subst hn; simp; linarith [Real.log_pos (show (1 : ℝ) < 32 by norm_num)]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have ha_pos : (0 : ℝ) < numGridConvex n n := Nat.cast_pos.mpr (numGridConvex_pos n n)
    have hle : (numGridConvex n n : ℝ) ≤ 32 ^ n := by exact_mod_cast numGridConvex_le_exp n
    have hlog : Real.log (numGridConvex n n : ℝ) ≤ ↑n * Real.log 32 := by
      calc Real.log ↑(numGridConvex n n)
          ≤ Real.log ((32 : ℝ) ^ n) := Real.log_le_log ha_pos hle
        _ = ↑n * Real.log 32 := by rw [Real.log_pow]
    show -Real.log ↑(numGridConvex n n) / ↑n ≥ -Real.log 32
    rw [ge_iff_le, neg_div, neg_le_neg_iff]
    rw [mul_comm] at hlog
    exact div_le_of_le_mul₀ (le_of_lt hn') (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 32)) hlog

/-! ## The growth constant via Fekete's lemma -/

theorem growth_constant_exists :
    ∃ ρ : ℝ, Tendsto (fun n => -Real.log (numGridConvex n n : ℝ) / ↑n) atTop (nhds ρ) :=
  ⟨neg_log_subadditive.lim, neg_log_subadditive.tendsto_lim bddBelow_neg_log_div⟩

theorem growth_constant_log :
    ∃ ρ : ℝ,
      Tendsto (fun n => Real.log (numGridConvex n n : ℝ) / ↑n) atTop (nhds ρ) := by
  obtain ⟨L, hL⟩ := growth_constant_exists
  exact ⟨-L, by simpa [neg_div] using hL.neg⟩

theorem growth_rate_is_lower_bound {m : ℕ} (hm : m ≠ 0) :
    neg_log_subadditive.lim ≤ -Real.log (numGridConvex m m : ℝ) / m :=
  neg_log_subadditive.lim_le_div bddBelow_neg_log_div hm

end CausalAlgebraicGeometry.GrowthConstant
