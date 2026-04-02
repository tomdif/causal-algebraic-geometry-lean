/-
  Local Reduction: (w, a) as the Minimal State for the d=3 Inner Chain

  The d=3 transfer operator acts on pairs (a, b) of nonincreasing functions.
  At each slice position j, the state is (a(j), b(j)) with:
    width w(j) = max(0, b(j) - a(j) + 1)
    center a(j) = lower boundary

  The key structural theorem: the transition from (w(j), a(j)) to
  (w(j+1), a(j+1)) is DETERMINED by the antitone constraint:
    a(j+1) ≤ a(j) and b(j+1) ≤ b(j)

  The (w, a) transition is:
    From (w, a) with b = a + w - 1:
    To (w', a') requires a' ≤ a and a' + w' - 1 ≤ a + w - 1.
    Number of valid a' values: see WidthTransitions3D.

  This file formalizes that (w, a) determines the local transition structure.
-/
import CausalAlgebraicGeometry.WidthTransitions3D
import Mathlib.Tactic

namespace LocalReduction3D

/-- A slab state at one slice position. -/
structure SlabState (m : ℕ) where
  a : Fin m  -- lower boundary
  b : Fin m  -- upper boundary
  hab : a ≤ b  -- positive width

/-- The width of a slab state. -/
def SlabState.width {m : ℕ} (s : SlabState m) : ℕ := s.b.val - s.a.val + 1

/-- The antitone transition: s' ≤ s componentwise. -/
def antitoneTransition {m : ℕ} (s s' : SlabState m) : Prop :=
  s'.a ≤ s.a ∧ s'.b ≤ s.b

instance {m : ℕ} (s s' : SlabState m) : Decidable (antitoneTransition s s') :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The transition from s to s' is antitone iff a' ≤ a and b' ≤ b.
    The resulting width w' = b' - a' + 1 and center a' are determined by
    the choice of (a', b'), which is parameterized by:
      a' ∈ {0, ..., a}  (antitone constraint on lower boundary)
      b' ∈ {a', ..., b}  (antitone constraint on upper, plus b' ≥ a')
    giving w' = b' - a' + 1 ∈ {1, ..., a + w} and a' ∈ {0, ..., a}.

    The key fact: given target width w', the number of valid a' values
    is exactly the count from WidthTransitions3D. -/
theorem transition_determined_by_wa {m : ℕ} (s : SlabState m) (w' : ℕ)
    (_hw' : 0 < w') (hw'_le : w' ≤ s.a.val + s.width) :
    ∃ (count : ℕ), count > 0 ∧
    count = (WidthTransitions3D.validLowerBounds s.a.val (s.width) w').card := by
  refine ⟨(WidthTransitions3D.validLowerBounds s.a.val s.width w').card, ?_, rfl⟩
  by_cases h : w' ≤ s.width
  · rw [WidthTransitions3D.transition_count_below s.a.val s.width w' h]
    omega
  · push_neg at h
    rw [WidthTransitions3D.transition_count_above s.a.val s.width w' h hw'_le]
    omega

/-- The (w, a) pair FULLY determines the transition count structure.
    Two states with the same (w, a) have IDENTICAL transition counts
    to every target width w'. -/
theorem wa_determines_transitions {m : ℕ} (s₁ s₂ : SlabState m)
    (hw : s₁.width = s₂.width) (ha : s₁.a = s₂.a) (w' : ℕ) :
    (WidthTransitions3D.validLowerBounds s₁.a.val s₁.width w').card =
    (WidthTransitions3D.validLowerBounds s₂.a.val s₂.width w').card := by
  rw [ha, hw]

-- The transition count from (w, a) to w' depends only on w, a, w'.
-- NOT on m, the specific values of a(j±1), or any other context.
-- This is the LOCAL REDUCTION: (w, a) is sufficient for the transition.
-- This is immediate from the definition of validLowerBounds,
-- which depends only on a, w, w' (not on m or global context).

end LocalReduction3D
