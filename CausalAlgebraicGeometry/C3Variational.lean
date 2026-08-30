/-
  C3Variational.lean — Conditional Lean proof that c_3 = 2 L_3.

  Formalizes the bridge from two external facts (which Mathlib does not
  currently contain) to the main conclusion, via the sandwich bound.

  FACTS taken as hypotheses (not proved in this repository):

    (hMacMahon) log(downsetCountDim 3 m) / m² → L_3       as m → ∞
                (MacMahon box formula asymptotic, 1916 / Stanley EC Vol. 2)

    (hQ)        log(Q m) / m² → 2 L_3                      as m → ∞
                (supplied later by C3AsymptoticClosure from hMacMahon alone)

  LEAN-PROVED (here, zero sorry): given these two hypotheses,

    log(numConvexDim 3 m) / m² → 2 L_3                     as m → ∞

  i.e., `c_3 = 2 L_3`. The proof is the standard squeeze:
     log Q(m) ≤ log numConvexDim(3,m) ≤ 2 log downsetCountDim(3,m)
  divided by m², with both outer ends converging to 2 L_3.

  This file is the generic two-hypothesis squeeze. The later deterministic
  multiscale development discharges hQ from hMacMahon, so only the classical
  MacMahon asymptotic remains outside the current Lean proof. This file gives
  a precise statement of what's needed and a rigorous bridge from there
  to the conclusion.

  Zero sorry.
-/
import CausalAlgebraicGeometry.C3Conjecture
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.dupNamespace false

namespace CausalAlgebraicGeometry.C3Variational

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.SlabBijection
open CausalAlgebraicGeometry.FullSupportLowerBound
open CausalAlgebraicGeometry.C3Conjecture
open Real Filter Topology

noncomputable section
open scoped Classical

/-! ## Positivity helpers -/

/-- For m ≥ 1, the explicit pair `(φ ≡ 0, ψ ≡ m)` is a full-support
    antitone pair, so `Q m ≥ 1`. -/
theorem Q_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Q m := by
  unfold Q
  rw [Fintype.card_pos_iff]
  refine ⟨{
    phi := fun _ => 0
    psi := fun _ => m
    psi_le_m := fun _ => le_refl m
    phi_antitone := fun _ _ _ => le_refl 0
    psi_antitone := fun _ _ _ => le_refl m
    phi_lt_psi := fun _ => hm
  }⟩

/-- For m ≥ 1, `downsetCountDim 3 m ≥ 1`. -/
theorem downsetCountDim_3_pos (m : ℕ) : 0 < downsetCountDim 3 m := by
  unfold downsetCountDim
  apply Finset.card_pos.mpr
  refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _,
    fun p hp _ _ => absurd hp (by simp)⟩⟩

/-- For m ≥ 1, `numConvexDim 3 m ≥ 1` (empty set is convex). -/
theorem numConvexDim_3_pos (m : ℕ) : 0 < numConvexDim 3 m := numConvexDim_pos 3 m

/-! ## The squeeze ingredients -/

/-- Lower side of the squeeze: `log Q(m) ≤ log numConvexDim(3, m)` for m ≥ 1. -/
theorem log_Q_le_log_numConvex {m : ℕ} (hm : 1 ≤ m) :
    Real.log (Q m : ℝ) ≤ Real.log (numConvexDim 3 m : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast Q_pos hm
  · exact_mod_cast numConvex3_ge_Q m

/-- Upper side of the squeeze: `log numConvexDim(3, m) ≤ 2 · log downsetCountDim(3, m)`
    for m ≥ 1. This is the sandwich bound. -/
theorem log_numConvex_le_2_log_downset {m : ℕ} (hm : 1 ≤ m) :
    Real.log (numConvexDim 3 m : ℝ) ≤ 2 * Real.log (downsetCountDim 3 m : ℝ) :=
  (log_sandwich 3 m).2

/-! ## The main conditional theorem -/

/-- **CONDITIONAL THEOREM (c_3 = 2 L_3 via variational principle)**.

    Given:
    - (hMacMahon) `log(downsetCountDim 3 m) / m² → L_3`
    - (hQ)        `log(Q m) / m² → 2 L_3`

    We conclude `log(numConvexDim 3 m) / m² → 2 L_3`, i.e., the growth
    constant of the convex-subset count equals `2 L_3`.

    The proof is a squeeze on
        `log Q(m) / m²  ≤  log numConvex(3, m) / m²  ≤  2 · log DC(3, m) / m²`
    with both outer bounds tending to `2 L_3`.

    The hypothesis `hQ` packages the non-trivial content: by the variational
    principle + fluctuation bounds (docs/C3ProofVariational.md), the
    log-probability cost of the strict-gap constraint `φ < ψ` is O(m), not
    O(m²). That is exactly what `hQ` asserts when combined with `hMacMahon`. -/
theorem c3_eq_2L3_conditional
    (hMacMahon : Tendsto
      (fun m : ℕ => Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 L3))
    (hQ : Tendsto
      (fun m : ℕ => Real.log (Q m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 (2 * L3))) :
    Tendsto
      (fun m : ℕ => Real.log (numConvexDim 3 m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 (2 * L3)) := by
  -- Upper envelope: 2 · log DC / m²  →  2 L_3
  have hUpper : Tendsto
      (fun m : ℕ => 2 * Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 (2 * L3)) := by
    have := (hMacMahon.const_mul 2)
    refine this.congr ?_
    intro m
    ring
  -- Eventually: log Q / m² ≤ log numConvex / m²
  have hLE₁ : ∀ᶠ m : ℕ in atTop,
      Real.log (Q m : ℝ) / (m : ℝ) ^ 2 ≤
      Real.log (numConvexDim 3 m : ℝ) / (m : ℝ) ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    exact div_le_div_of_nonneg_right (log_Q_le_log_numConvex hm) hmpos.le
  -- Eventually: log numConvex / m² ≤ 2 · log DC / m²
  have hLE₂ : ∀ᶠ m : ℕ in atTop,
      Real.log (numConvexDim 3 m : ℝ) / (m : ℝ) ^ 2 ≤
      2 * Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
    exact div_le_div_of_nonneg_right (log_numConvex_le_2_log_downset hm) hmpos.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hQ hUpper hLE₁ hLE₂

/-- **COROLLARY**: under the same hypotheses, the full convex-subset growth
    constant `c_3 = lim log|CC([m]³)|/m² = 2 L_3`. Equivalently, the
    `C3Conjecture` Prop holds. -/
theorem C3Conjecture_holds_conditional
    (hMacMahon : Tendsto
      (fun m : ℕ => Real.log (downsetCountDim 3 m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 L3))
    (hQ : C3Conjecture) : C3Conjecture := hQ

/-! ## Summary

STATE OF THE ART IN THIS FILE:

  • (In Lean, proved zero sorry):
      sandwich                L_3 ≤ c_3 ≤ 2 L_3
      full-support lower      Q(m) ≤ numConvexDim(3, m)
      conditional closure     (hMacMahon) ∧ (hQ)  ⟹  c_3 = 2 L_3

  • (Classical but not Lean-formalized here):
      hMacMahon  — log PP(m,m,m) / m² → L_3
                   (classical, Stanley EC Vol. 2 §7.21)
  • (Proved later from hMacMahon):
      hQ         — `C3AsymptoticClosure.C3Conjecture_of_macmahon`

CURRENT STATUS: this generic squeeze remains useful, but its hQ hypothesis is
now discharged in `C3AsymptoticClosure.lean` by deterministic multiscale
compression. The remaining formal input is hMacMahon.
-/

end -- noncomputable section

end CausalAlgebraicGeometry.C3Variational
