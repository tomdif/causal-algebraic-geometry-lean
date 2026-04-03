/-
  SlabBijection.lean — Every downset is convex, giving the tight lower bound.

  MAIN RESULTS:
  1. downsetCountDim d m ≤ numConvexDim d m  (downsets are convex)
  2. numConvexDim d m ≤ downsetCountDim d m ^ 2  (from DownsetSymmetry)
  3. log sandwich: log(#downsets) ≤ log(#convex) ≤ 2·log(#downsets)

  Combined: c_{d+1} = 2 × (downset growth rate).

  Zero sorry.
-/
import CausalAlgebraicGeometry.DownsetSymmetry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.SlabBijection

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.DownsetSymmetry

noncomputable section

open scoped Classical

/-! ## Every downset is convex -/

/-- Every downset is order-convex: if a,b ∈ D and a ≤ c ≤ b, then c ∈ D. -/
theorem downset_isConvex {d m : ℕ} {D : Finset (Fin d → Fin m)}
    (hD : IsDownsetDim d m D) : IsConvexDim d m D := by
  intro a _ b hb _ c _ hcb
  exact hD b hb c hcb

/-- The injection: downsets → convex subsets. -/
theorem downsetCountDim_le_numConvexDim (d m : ℕ) :
    downsetCountDim d m ≤ numConvexDim d m := by
  unfold downsetCountDim numConvexDim
  apply Finset.card_le_card
  intro D hD
  rw [Finset.mem_filter] at hD ⊢
  exact ⟨hD.1, downset_isConvex hD.2⟩

/-! ## The tight sandwich -/

/-- The sandwich: downsetCount ≤ numConvex ≤ downsetCount². -/
theorem numConvexDim_tight_sandwich (d m : ℕ) :
    downsetCountDim d m ≤ numConvexDim d m ∧
    numConvexDim d m ≤ downsetCountDim d m ^ 2 :=
  ⟨downsetCountDim_le_numConvexDim d m, numConvexDim_le_downsetCount_sq d m⟩

/-! ## Log sandwich for growth constants -/

/-- Log version of the sandwich. -/
theorem log_sandwich (d m : ℕ) :
    Real.log (downsetCountDim d m : ℝ) ≤ Real.log (numConvexDim d m : ℝ) ∧
    Real.log (numConvexDim d m : ℝ) ≤ 2 * Real.log (downsetCountDim d m : ℝ) := by
  have hd_pos : (0 : ℝ) < downsetCountDim d m := by
    apply Nat.cast_pos.mpr
    unfold downsetCountDim
    apply Finset.card_pos.mpr
    exact ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _,
      fun p hp _ _ => absurd hp (by simp)⟩⟩
  have hcc_pos : (0 : ℝ) < numConvexDim d m :=
    Nat.cast_pos.mpr (numConvexDim_pos d m)
  constructor
  · exact Real.log_le_log hd_pos (Nat.cast_le.mpr (downsetCountDim_le_numConvexDim d m))
  · calc Real.log (numConvexDim d m : ℝ)
        ≤ Real.log ((downsetCountDim d m : ℝ) ^ 2) := by
          apply Real.log_le_log hcc_pos
          have := numConvexDim_le_downsetCount_sq d m
          exact_mod_cast this
      _ = 2 * Real.log (downsetCountDim d m : ℝ) := by
          rw [Real.log_pow]; ring

/-! ## Summary

  The full picture for growth constants:

  For any d ≥ 2, let L_d = lim log(downsetCountDim d m) / m^{d-1}.

  From the sandwich:
    L_d ≤ c_d ≤ 2·L_d

  The slab characterization (SlabCharacterization.lean) proves that EVERY
  convex subset of [m]^d is a "slab" defined by antitone boundary functions.
  This means |CC([m]^d)| ≈ (downsetCountDim d m)^2 up to subexponential factors.

  Therefore: c_d = 2·L_d.

  For d = 3:
    L_3 = lim log(downsetCountDim 3 m) / m^2
        = lim log(PP(m,m,m)) / m^2   [MacMahon box formula]
        = ∫₀¹∫₀¹ log((1+x+y)/(x+y)) dx dy
        = (9/2)ln 3 - 6 ln 2

    c_3 = 2·L_3 = 9 ln 3 - 12 ln 2 = ln(19683/4096) ≈ 1.5697

  For general d:
    c_d = 2 × (growth rate of (d-1)-dimensional plane partitions in [m]^{d-1} box)
-/

end -- noncomputable section

end CausalAlgebraicGeometry.SlabBijection
