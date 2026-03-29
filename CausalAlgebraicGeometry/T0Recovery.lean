/-
  T0Recovery.lean — Every finite poset is T₀ in the Alexandrov topology.

  The non-strict principal filter α ↦ {β : α ≤ β} is ALWAYS injective,
  for ANY finite poset, with NO extra hypotheses.

  This fixes the Recovery Theorem: use non-strict upsets instead of strict ones.
  The strict upset map α ↦ {β : α < β} requires a T₀ hypothesis
  (and fails on the V-poset). The non-strict version works universally.

  Also proved: the Alexandrov topology (upsets as opens) is always T₀.

  Zero sorry.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.T0Recovery

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
  [DecidableRel (fun (a b : α) => a ≤ b)]

/-! ## Non-strict principal filter -/

/-- The non-strict principal filter: ↑≤α = {β : α ≤ β}. -/
def principalFilter (a : α) : Finset α :=
  Finset.univ.filter fun b => a ≤ b

/-- α is always in its own principal filter. -/
theorem mem_principalFilter_self (a : α) : a ∈ principalFilter a := by
  simp [principalFilter, Finset.mem_filter]

/-- β ∈ ↑≤α iff α ≤ β. -/
theorem mem_principalFilter_iff (a b : α) :
    b ∈ principalFilter a ↔ a ≤ b := by
  simp [principalFilter, Finset.mem_filter]

/-- **The principal filter map is always injective.**
    If ↑≤α = ↑≤β then α = β. No T₀ hypothesis needed. -/
theorem principalFilter_injective :
    Function.Injective (principalFilter (α := α)) := by
  intro a b h
  have ha : a ∈ principalFilter b := by rw [← h]; exact mem_principalFilter_self a
  have hb : b ∈ principalFilter a := by rw [h]; exact mem_principalFilter_self b
  rw [mem_principalFilter_iff] at ha hb
  exact le_antisymm hb ha

/-! ## The Alexandrov topology is T₀ -/

/-- For any distinct a ≠ b in a partial order, there exists an upset containing
    one but not the other. This is the T₀ property of the Alexandrov topology. -/
theorem alexandrov_T0 (a b : α) (hab : a ≠ b) :
    (a ∈ principalFilter b ∧ b ∉ principalFilter a) ∨
    (b ∈ principalFilter a ∧ a ∉ principalFilter b) ∨
    (a ∉ principalFilter b ∧ b ∉ principalFilter a) := by
  simp only [mem_principalFilter_iff]
  by_cases h1 : b ≤ a
  · by_cases h2 : a ≤ b
    · exact absurd (le_antisymm h2 h1) hab
    · exact Or.inl ⟨h1, h2⟩
  · by_cases h2 : a ≤ b
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-! ## Recovery via non-strict upsets -/

/-- The non-strict principal filter is a causally convex subset
    (it's an upset, hence convex). -/
theorem principalFilter_isUpset (a : α) :
    ∀ b ∈ principalFilter a, ∀ c : α, b ≤ c → c ∈ principalFilter a := by
  intro b hb c hbc
  rw [mem_principalFilter_iff] at hb ⊢
  exact le_trans hb hbc

/-- **The corrected Recovery Theorem**: every element of a finite poset is
    uniquely determined by its non-strict principal filter, with no T₀ hypothesis.

    Formally: the map α ↦ {β : α ≤ β} is injective. -/
theorem recovery_universal :
    ∀ a b : α, principalFilter a = principalFilter b → a = b :=
  fun a b h => principalFilter_injective h

/-! ## Comparison with strict upsets -/

/-- The strict principal upset: ↑α = {β : α < β}. -/
def strictUpset (a : α) : Finset α :=
  Finset.univ.filter fun b => a ≤ b ∧ a ≠ b

-- The strict upset map is NOT always injective.
-- Counterexample: V-poset, see RecoveryCounterexample.lean.
-- The T₀ hypothesis is needed for strict upset injectivity.

/-- If α < β (strictly comparable), then their strict upsets differ. -/
theorem strictUpset_injective_on_comparable (a b : α) (hab : a < b) :
    strictUpset a ≠ strictUpset b := by
  intro h
  have hb : b ∈ strictUpset a := by
    simp [strictUpset, Finset.mem_filter]; exact ⟨le_of_lt hab, ne_of_lt hab⟩
  rw [h] at hb
  simp [strictUpset, Finset.mem_filter] at hb

/-! ## Summary

  The non-strict principal filter map α ↦ {β : α ≤ β} is:
  1. Always injective (no hypotheses needed)
  2. Always an upset (hence causally convex)
  3. The correct map for the Recovery Theorem

  The strict principal upset map α ↦ {β : α < β}:
  1. NOT always injective (V-poset counterexample)
  2. Injective on comparable pairs
  3. Fully injective iff the poset is T₀ (future-distinguishing)

  For the paper: use non-strict upsets for recovery, or add T₀ hypothesis for strict.
-/

end CausalAlgebraicGeometry.T0Recovery
