/-
  Width Transitions for the d=3 Spectral Theory

  Theorem C: The exact transition count for the (width, center) chain
  in the d=3 comparability transfer operator.

  Given a slab state (a, b) at slice position j, with width w = b - a + 1
  and center a, the transition to (a', b') at position j+1 requires
  a' ≤ a and b' ≤ b (antitone constraint). The number of valid
  transitions to target width w' is:

    a + 1              if w' ≤ w (and w' > 0)
    a + w - w' + 1     if w < w' ≤ a + w
    0                  if w' > a + w
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace WidthTransitions3D

/-- The set of valid lower boundaries a' for a transition from state (a, a+w-1)
to target width w'. The constraint is a' ≤ a and a' + w' - 1 ≤ a + w - 1. -/
def validLowerBounds (a w w' : ℕ) : Finset ℕ :=
  (Finset.range (a + 1)).filter (fun a' => a' + w' ≤ a + w)

/-- When w' ≤ w, the constraint a' + w' ≤ a + w is automatic for a' ≤ a. -/
theorem filter_trivial (a w w' : ℕ) (hw' : w' ≤ w) :
    validLowerBounds a w w' = Finset.range (a + 1) := by
  simp only [validLowerBounds]
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, by omega⟩

/-- Theorem C (below diagonal): #transitions from (a, w) to w' is a+1 when w' ≤ w. -/
theorem transition_count_below (a w w' : ℕ) (hw' : w' ≤ w) :
    (validLowerBounds a w w').card = a + 1 := by
  rw [filter_trivial a w w' hw', Finset.card_range]

/-- When w' > w, only a' ≤ a + w - w' works. -/
theorem filter_binding (a w w' : ℕ) (hw : w < w') (hb : w' ≤ a + w) :
    validLowerBounds a w w' = Finset.range (a + w - w' + 1) := by
  simp only [validLowerBounds]
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨h1, h2⟩; omega
  · intro h; constructor <;> omega

/-- Theorem C (above diagonal): #transitions from (a, w) to w' is a+w-w'+1
when w < w' ≤ a + w. -/
theorem transition_count_above (a w w' : ℕ) (hw : w < w') (hb : w' ≤ a + w) :
    (validLowerBounds a w w').card = a + w - w' + 1 := by
  rw [filter_binding a w w' hw hb, Finset.card_range]

/-- Theorem C (out of range): no transitions when w' > a + w. -/
theorem transition_count_zero (a w w' : ℕ) (h : a + w < w') :
    (validLowerBounds a w w').card = 0 := by
  simp only [validLowerBounds, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  omega

end WidthTransitions3D
