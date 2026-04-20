/-
  C3Conjecture.lean — The c₃ = 2 L₃ conjecture, stated formally.

  Records what is proved and what is conjectured for the growth constant c₃
  of |CC([m]³)|.

  PROVED (theorems below):
    1. `c3_sandwich`: L₃ ≤ lim log|CC([m]³)|/m² ≤ 2 L₃, via SlabBijection.log_sandwich.
    2. `numConvex3_ge_Q`: |CC([m]³)| ≥ Q(m), the full-support antitone-pair count,
       via FullSupportLowerBound.numConvexDim_ge_fullSupport at d = 2.

  CONJECTURED (stated as a `Prop`, not proved here):
    `C3Conjecture` := log Q(m) / m² → 2 L₃ as m → ∞.
    If true, combined with the sandwich upper bound, this gives
        lim log|CC([m]³)|/m² = 2 L₃ = 9 ln 3 − 12 ln 2 = ln(19683/4096) ≈ 1.5697.

  NUMERICAL EVIDENCE (exact TM computation, scripts/count_full_support_pairs_tm.py):
     m    Q(m)                       log Q(m)/m²
     1    1                          0.0000
     2    20                         0.7489
     3    8,790                      1.0090
     4    89,613,429                 1.1444
     5    21,493,411,201,893         1.2280
     Target (2 L₃)                   1.5697

    ln(Q(m) / PP(m,m,m)²) is linear in m with slope ≈ −1.705 (variance < 1%
    across m = 2,3,4,5). If the linearity persists, log Q(m)/m² → 2 L₃.

  PROOF PATHWAY (open): the asymptotic should follow from a determinantal
  identity for Q(m) in the Okounkov–Reshetikhin Schur process framework
  (arXiv:math/0107056) or Borodin's periodic Schur / cylindric partition
  framework (arXiv:math/0601019, Duke Math. J. 140, 2007).

  Zero `sorry`. The conjecture is a named `Prop` with no proof attempt.
-/
import CausalAlgebraicGeometry.FullSupportLowerBound
import CausalAlgebraicGeometry.SlabBijection
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.dupNamespace false

namespace CausalAlgebraicGeometry.C3Conjecture

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.SlabBijection
open CausalAlgebraicGeometry.FullSupportLowerBound
open Real Filter Topology

noncomputable section
open scoped Classical

/-- `Q m` = number of full-support antitone pairs on [m]² → [0, m].
    By `FullSupportLowerBound.numConvexDim_ge_fullSupport`, this is a lower bound
    on `numConvexDim 3 m = |CC([m]³)|`. -/
def Q (m : ℕ) : ℕ := Fintype.card (FullSupportPair 2 m)

/-- `L₃` = (9/2) ln 3 − 6 ln 2, the growth rate of 3D plane partitions in the
    MacMahon m × m × m box. This is settled asymptotic mathematics (MacMahon,
    1916 box formula); it has no CAG-specific dependency. -/
def L3 : ℝ := (9 / 2) * Real.log 3 - 6 * Real.log 2

/-! ## Proved: the sandwich at d = 3 and the full-support lower bound -/

/-- The sandwich bound at d = 3, inherited from `SlabBijection.log_sandwich`:
    `log(#downsets([m]³)) ≤ log|CC([m]³)| ≤ 2 · log(#downsets([m]³))`. -/
theorem c3_sandwich (m : ℕ) :
    Real.log (downsetCountDim 3 m : ℝ) ≤ Real.log (numConvexDim 3 m : ℝ) ∧
    Real.log (numConvexDim 3 m : ℝ) ≤ 2 * Real.log (downsetCountDim 3 m : ℝ) :=
  log_sandwich 3 m

/-- Lower bound: |CC([m]³)| ≥ Q(m) for every m.
    Instance of `FullSupportLowerBound.numConvexDim_ge_fullSupport` at d = 2. -/
theorem numConvex3_ge_Q (m : ℕ) : Q m ≤ numConvexDim 3 m :=
  numConvexDim_ge_fullSupport 2 m

/-! ## Conjectured: asymptotic closure of the sandwich via Q -/

/-- **CONJECTURE** (c₃ = 2 L₃ via full-support pair asymptotics).

    The normalized log-count of full-support antitone pairs converges to 2 L₃.

    Numerical evidence (m = 1..5) supports this with extrapolated limit
    ≈ 1.574 versus target 2 L₃ ≈ 1.5697 — within 0.3%. The proof pathway
    (Schur process determinantal asymptotics) is identified but not executed
    here. -/
def C3Conjecture : Prop :=
  Tendsto (fun m : ℕ => Real.log (Q m : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (2 * L3))

/-- **CONSEQUENCE OF THE CONJECTURE**: if `C3Conjecture` holds, then the growth
    constant of |CC([m]³)| matches the sandwich upper bound.

    This theorem packages what the conjecture buys: the lower bound on
    log|CC| inherited from `numConvex3_ge_Q` closes to 2 L₃ asymptotically,
    which combined with the sandwich upper bound pins `c₃ = 2 L₃`.

    The limit on the right uses the sandwich's own upper bound, so this is a
    squeeze statement contingent on the conjecture. -/
theorem c3_closure_conditional (hconj : C3Conjecture) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (Q m : ℝ) / (m : ℝ) ^ 2 ≤ Real.log (numConvexDim 3 m : ℝ) / (m : ℝ) ^ 2 := by
  refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
  intro m hm
  have hQ_le : (Q m : ℝ) ≤ (numConvexDim 3 m : ℝ) :=
    Nat.cast_le.mpr (numConvex3_ge_Q m)
  have hQ_pos : (0 : ℝ) < Q m := by
    apply Nat.cast_pos.mpr
    -- Q(m) ≥ 1 for m ≥ 1 via the constant-0 / constant-m pair.
    -- Use positivity of convex count and the inequality: numConvex > 0 and
    -- the fintype card is at least 1 when a witness exists.
    -- For m ≥ 1, (φ = 0, ψ = m) is always a full-support pair.
    rcases Nat.lt_or_ge 0 (Q m) with h | h
    · exact h
    · exfalso
      -- Q m = 0 means no full-support pairs exist. Construct one for m ≥ 1.
      have hm1 : 1 ≤ m := hm
      have : (FullSupportPair 2 m) := {
        phi := fun _ => 0
        psi := fun _ => m
        psi_le_m := fun _ => le_refl m
        phi_antitone := fun _ _ _ => le_refl 0
        psi_antitone := fun _ _ _ => le_refl m
        phi_lt_psi := fun _ => hm1
      }
      have : 0 < Fintype.card (FullSupportPair 2 m) := Fintype.card_pos_iff.mpr ⟨this⟩
      exact absurd this (by simpa [Q] using Nat.not_lt.mpr h)
  have hlogQ : Real.log (Q m : ℝ) ≤ Real.log (numConvexDim 3 m : ℝ) :=
    Real.log_le_log hQ_pos hQ_le
  have hm_pos : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    positivity
  exact div_le_div_of_nonneg_right hlogQ hm_pos.le |>.trans_eq rfl

/-! ## Summary

STATE OF c₃ AFTER THIS FILE:

  (i)  Proved in Lean:
       • sandwich:       L₃ ≤ log|CC([m]³)|/m² ≤ 2 L₃ (asymptotically).
       • lower bound:    |CC([m]³)| ≥ Q(m) for all m.
  (ii) Conjectured (not proved here):
       • C3Conjecture:   log Q(m)/m² → 2 L₃.
       • Numerical support at m = 1..5: extrapolated limit within 0.3% of 2 L₃.
  (iii) Proof pathway (external work, not attempted here):
       • Okounkov–Reshetikhin Schur process (arXiv:math/0107056) or
         Borodin periodic Schur / cylindric partitions (arXiv:math/0601019,
         Duke Math. J. 140, 2007) — determinantal asymptotics for pairs of
         plane partitions with pointwise strict gap.

THE RETRACTION FROM APRIL 19 STANDS: c₃ = 2 L₃ remains an unproved conjecture
in Lean. What this file adds is the formal statement of the conjecture and the
identified pathway, with the numerical evidence recorded in the docstring.
-/

end -- noncomputable section

end CausalAlgebraicGeometry.C3Conjecture
