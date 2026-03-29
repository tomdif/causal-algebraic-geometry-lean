/-
  RecoveryCounterexample.lean — The V-poset shows h_not_max is insufficient for recovery.

  The V-poset: {0, 1, 2} with 0 < 2 and 1 < 2 (element 2 is maximum, 0 ∥ 1).
  Both 0 and 1 are non-maximal, but ↑0 = {2} = ↑1.
  So the map α ↦ ↑α is NOT injective on non-maximal elements.
  The T₀ (future-distinguishing) hypothesis is NECESSARY for injectivity.

  Zero sorry.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.RecoveryCounterexample

/-- The V-poset order on Fin 3: 0 ≤ 0, 1 ≤ 1, 2 ≤ 2, 0 ≤ 2, 1 ≤ 2. -/
def vLe : Fin 3 → Fin 3 → Prop := fun a b =>
  a = b ∨ (a.val = 0 ∧ b.val = 2) ∨ (a.val = 1 ∧ b.val = 2)

instance : DecidableRel vLe := fun a b => by unfold vLe; exact inferInstance

/-- The strict principal upset: {β | α < β} = {β | α ≤ β ∧ α ≠ β}. -/
def strictUpset (a : Fin 3) : Finset (Fin 3) :=
  Finset.univ.filter fun b => vLe a b ∧ a ≠ b

/-- 0 is non-maximal: 0 < 2. -/
theorem zero_not_max : ∃ b : Fin 3, vLe 0 b ∧ (0 : Fin 3) ≠ b := by
  exact ⟨2, Or.inr (Or.inl ⟨rfl, rfl⟩), by decide⟩

/-- 1 is non-maximal: 1 < 2. -/
theorem one_not_max : ∃ b : Fin 3, vLe 1 b ∧ (1 : Fin 3) ≠ b := by
  exact ⟨2, Or.inr (Or.inr ⟨rfl, rfl⟩), by decide⟩

/-- ↑0 = {2}. -/
theorem upset_zero : strictUpset 0 = {2} := by native_decide

/-- ↑1 = {2}. -/
theorem upset_one : strictUpset 1 = {2} := by native_decide

/-- The strict upsets of 0 and 1 are EQUAL, despite 0 ≠ 1. -/
theorem upsets_equal : strictUpset 0 = strictUpset 1 := by
  rw [upset_zero, upset_one]

/-- 0 ≠ 1 in Fin 3. -/
theorem zero_ne_one : (0 : Fin 3) ≠ 1 := by decide

/-- **The Recovery Counterexample**: two distinct non-maximal elements with equal strict upsets.
    This shows the h_not_max hypothesis is INSUFFICIENT for injectivity of α ↦ ↑α.
    The IsFutureDistinguishing (T₀) hypothesis is NECESSARY. -/
theorem recovery_counterexample :
    (0 : Fin 3) ≠ (1 : Fin 3) ∧
    (∃ b, vLe 0 b ∧ (0 : Fin 3) ≠ b) ∧
    (∃ b, vLe 1 b ∧ (1 : Fin 3) ≠ b) ∧
    strictUpset 0 = strictUpset 1 :=
  ⟨zero_ne_one, zero_not_max, one_not_max, upsets_equal⟩

/-- The V-poset is NOT future-distinguishing. -/
theorem v_poset_not_T0 :
    ¬ (∀ a b : Fin 3, a ≠ b → strictUpset a ≠ strictUpset b) := by
  push_neg
  exact ⟨0, 1, zero_ne_one, upsets_equal⟩

end CausalAlgebraicGeometry.RecoveryCounterexample
