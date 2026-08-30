/-
  C3AsymptoticClosure.lean — Analytic closure of deterministic multiscale
  compression.

  This file proves that the CAG-specific conjecture `log Q(m)/m² -> 2 L₃`
  follows from the single classical cubic plane-partition asymptotic

      log(downsetCountDim 3 m)/m² -> L₃.

  Unlike the former route, no limit-shape theorem or lozenge-height coordinate
  bridge is assumed.  The correction comes from C3MultiscaleCompression and is
  bounded using `k = floor(sqrt(m)) + 1`.

  Thus the only remaining external formalization target for the numerical
  identity c₃ = 2L₃ is MacMahon's cubic-box asymptotic itself.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.C3MultiscaleCompression
import CausalAlgebraicGeometry.C3Variational
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt

namespace CausalAlgebraicGeometry.C3AsymptoticClosure

open CausalAlgebraicGeometry.C3BarrierLowerBound
open CausalAlgebraicGeometry.C3Conjecture
open CausalAlgebraicGeometry.C3MultiscaleCompression
open CausalAlgebraicGeometry.C3ShiftCompression
open CausalAlgebraicGeometry.C3Variational
open CausalAlgebraicGeometry.DimensionLaw
open Real Filter Topology

noncomputable section
open scoped Classical

/-! ## The square-root scale has subarea cost -/

/-- The exponent in the power-of-four correction, using the everywhere
positive scale `k(m) = floor(sqrt(m)) + 1`. -/
def correctionExponent (m : ℕ) : ℕ :=
  1 + 2 * (m * (m / (Nat.sqrt m + 2))) +
    m * (Nat.sqrt m + 1) + m * (Nat.sqrt m + 2)

/-- The coarse height at square-root scale is no larger than `sqrt(m)`. -/
theorem coarse_height_le_sqrt (m : ℕ) :
    m / (Nat.sqrt m + 2) ≤ Nat.sqrt m := by
  by_contra h
  have hs : Nat.sqrt m + 1 ≤ m / (Nat.sqrt m + 2) := by omega
  have hmul := Nat.div_mul_le_self m (Nat.sqrt m + 2)
  have hprod : (Nat.sqrt m + 1) * (Nat.sqrt m + 2) ≤ m := by
    exact le_trans (Nat.mul_le_mul_right _ hs) hmul
  have hsqrt := Nat.lt_succ_sqrt m
  nlinarith

/-- A simple polynomial upper bound for the correction exponent. -/
theorem correctionExponent_le (m : ℕ) :
    correctionExponent m ≤ 1 + 4 * m * Nat.sqrt m + 3 * m := by
  unfold correctionExponent
  have h := coarse_height_le_sqrt m
  nlinarith

/-- The integer square root divided by its argument tends to zero. -/
theorem tendsto_natSqrt_div :
    Tendsto (fun m : ℕ => (Nat.sqrt m : ℝ) / (m : ℝ)) atTop (𝓝 0) := by
  have hsqrtTop :
      Tendsto (fun m : ℕ => Real.sqrt (m : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : ℕ => 1 / Real.sqrt (m : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hsqrtTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
  · filter_upwards with m
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hle : (Nat.sqrt m : ℝ) ≤ Real.sqrt (m : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    calc
      (Nat.sqrt m : ℝ) / (m : ℝ) ≤ Real.sqrt (m : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_right hle hmreal.le
      _ = 1 / Real.sqrt (m : ℝ) := Real.sqrt_div_self'

/-- The normalized multiscale correction is subarea. -/
theorem tendsto_correctionExponent_div_sq :
    Tendsto (fun m : ℕ => (correctionExponent m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hone : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have honeSq : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 0) := by
    convert hone.mul hone using 1
    · funext m
      ring
    · ring
  have hsqrt := tendsto_natSqrt_div
  have hupper : Tendsto
      (fun m : ℕ =>
        (1 : ℝ) / (m : ℝ) ^ 2 +
          4 * ((Nat.sqrt m : ℝ) / (m : ℝ)) + 3 / (m : ℝ))
      atTop (𝓝 0) := by
    convert honeSq.add ((hsqrt.const_mul 4).add
      (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ))) using 1 <;> ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards with m
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hcast : (correctionExponent m : ℝ) ≤
        (1 + 4 * m * Nat.sqrt m + 3 * m : ℕ) := by
      exact_mod_cast correctionExponent_le m
    calc
      (correctionExponent m : ℝ) / (m : ℝ) ^ 2 ≤
          (1 + 4 * m * Nat.sqrt m + 3 * m : ℕ) / (m : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcast (sq_nonneg _)
      _ = (1 : ℝ) / (m : ℝ) ^ 2 +
          4 * ((Nat.sqrt m : ℝ) / (m : ℝ)) + 3 / (m : ℝ) := by
        push_cast
        field_simp

/-- Multiplying the correction rate by the constant `log 4` still tends to
zero. -/
theorem tendsto_log_correction :
    Tendsto
      (fun m : ℕ =>
        ((correctionExponent m : ℝ) / (m : ℝ) ^ 2) * Real.log 4)
      atTop (𝓝 0) := by
  simpa using tendsto_correctionExponent_div_sq.mul_const (Real.log 4)

/-! ## Logarithmic squeeze for Q -/

/-- Finite lower logarithmic bound supplied by multiscale compression. -/
theorem two_log_downset_sub_correction_le_log_Q {m : ℕ} (hm : 1 ≤ m) :
    2 * Real.log (downsetCountDim 3 m : ℝ) -
        (correctionExponent m : ℝ) * Real.log 4 ≤
      Real.log (Q m : ℝ) := by
  have hfinite := downset_square_le_power_correction m (Nat.sqrt m + 1)
    (by omega) (by omega)
  change downsetCountDim 3 m ^ 2 ≤ Q m * 4 ^ correctionExponent m at hfinite
  have hDpos : (0 : ℝ) < (downsetCountDim 3 m : ℝ) := by
    exact_mod_cast downsetCountDim_3_pos m
  have hQpos : (0 : ℝ) < (Q m : ℝ) := by
    exact_mod_cast Q_pos hm
  have hcast : ((downsetCountDim 3 m : ℝ) ^ 2) ≤
      (Q m : ℝ) * (4 : ℝ) ^ correctionExponent m := by
    exact_mod_cast hfinite
  have hlog := Real.log_le_log (sq_pos_of_pos hDpos) hcast
  rw [Real.log_pow, Real.log_mul (ne_of_gt hQpos) (by positivity), Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-- Matching finite upper logarithmic bound from forgetting the strict order. -/
theorem log_Q_le_two_log_downset {m : ℕ} (hm : 1 ≤ m) :
    Real.log (Q m : ℝ) ≤ 2 * Real.log (downsetCountDim 3 m : ℝ) := by
  have hQpos : (0 : ℝ) < (Q m : ℝ) := by exact_mod_cast Q_pos hm
  have hcard := Q_le_profile_square m
  rw [card_antitoneProfile_eq_downsetCount] at hcard
  have hcast : (Q m : ℝ) ≤ (downsetCountDim 3 m : ℝ) ^ 2 := by
    exact_mod_cast hcard
  calc
    Real.log (Q m : ℝ) ≤ Real.log ((downsetCountDim 3 m : ℝ) ^ 2) :=
      Real.log_le_log hQpos hcast
    _ = 2 * Real.log (downsetCountDim 3 m : ℝ) := by
      rw [Real.log_pow]
      norm_num

/-! ## Unconditional entropy factorization -/

/-- **UNCONDITIONAL PAIR-ENTROPY THEOREM.**  The area-normalized entropy lost
by imposing strict pointwise order on a pair of cubic plane partitions tends
to zero.  This theorem has no MacMahon or limit-shape hypothesis. -/
theorem pair_entropy_gap_tendsto_zero :
    Tendsto
      (fun m : ℕ =>
        (2 * Real.log (downsetCountDim 3 m : ℝ) - Real.log (Q m : ℝ)) /
          (m : ℝ) ^ 2)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_log_correction
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmSq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    exact div_nonneg (sub_nonneg.mpr (log_Q_le_two_log_downset hm)) hmSq.le
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmSq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have h := two_log_downset_sub_correction_le_log_Q hm
    have hgap :
        2 * Real.log (downsetCountDim 3 m : ℝ) - Real.log (Q m : ℝ) ≤
          (correctionExponent m : ℝ) * Real.log 4 := by linarith
    have hdiv := div_le_div_of_nonneg_right hgap hmSq.le
    convert hdiv using 1 <;> ring

/-- **UNCONDITIONAL CAG ENTROPY FACTORIZATION.**  At area scale, a causal
convex subset of the cubic grid has the entropy of two independent boundary
surfaces.  MacMahon is needed only to evaluate their common numerical
constant, not for this factorization. -/
theorem convex_entropy_gap_tendsto_zero :
    Tendsto
      (fun m : ℕ =>
        (2 * Real.log (downsetCountDim 3 m : ℝ) -
          Real.log (numConvexDim 3 m : ℝ)) / (m : ℝ) ^ 2)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds pair_entropy_gap_tendsto_zero
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmSq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have hu := log_numConvex_le_2_log_downset hm
    exact div_nonneg (sub_nonneg.mpr hu) hmSq.le
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmSq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have hl := log_Q_le_log_numConvex hm
    apply div_le_div_of_nonneg_right _ hmSq.le
    linarith

/-- **CAG-SPECIFIC ASYMPTOTIC CLOSED.**  MacMahon's one-surface asymptotic
alone implies the full-support pair asymptotic.  The formerly independent
`hQ`/limit-shape hypothesis has disappeared. -/
theorem C3Conjecture_of_macmahon
    (hMacMahon : Tendsto
      (fun m : ℕ => Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 L3)) : C3Conjecture := by
  have hcenter : Tendsto
      (fun m : ℕ => 2 * Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 (2 * L3)) := by
    convert hMacMahon.const_mul 2 using 1 <;> ring
  have hlower : Tendsto
      (fun m : ℕ =>
        2 * Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2 -
          ((correctionExponent m : ℝ) / (m : ℝ) ^ 2) * Real.log 4)
      atTop (𝓝 (2 * L3)) := by
    convert hcenter.sub tendsto_log_correction using 1 <;> ring
  have hleLower : ∀ᶠ m : ℕ in atTop,
      2 * Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2 -
          ((correctionExponent m : ℝ) / (m : ℝ) ^ 2) * Real.log 4 ≤
        Real.log (Q m : ℝ) / (m : ℝ) ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmSq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have h := two_log_downset_sub_correction_le_log_Q hm
    have := div_le_div_of_nonneg_right h hmSq.le
    convert this using 1 <;> ring
  have hleUpper : ∀ᶠ m : ℕ in atTop,
      Real.log (Q m : ℝ) / (m : ℝ) ^ 2 ≤
        2 * Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmSq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (log_Q_le_two_log_downset hm) hmSq.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hcenter hleLower hleUpper

/-- Consequently, the convex-subset growth limit is `2L₃` under only the
classical MacMahon asymptotic. -/
theorem c3_eq_2L3_of_macmahon
    (hMacMahon : Tendsto
      (fun m : ℕ => Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 L3)) :
    Tendsto
      (fun m : ℕ => Real.log (numConvexDim 3 m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 (2 * L3)) :=
  c3_eq_2L3_conditional hMacMahon (C3Conjecture_of_macmahon hMacMahon)

end
end CausalAlgebraicGeometry.C3AsymptoticClosure
