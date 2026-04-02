/-
  Corollaries of Theorem C: properties of the (w, a) transition counts.

  From WidthTransitions3D:
    |validLowerBounds a w w'| = a + 1      for w' ≤ w
    |validLowerBounds a w w'| = a + w - w' + 1  for w < w' ≤ a + w
    |validLowerBounds a w w'| = 0          for w' > a + w

  Corollaries:
  1. Support: transitions exist iff 0 ≤ w' ≤ a + w
  2. Total outgoing count: Σ_{w'=0}^{a+w} |valid(w')| = (a+1)(a+2w)/2 + (a+1)
  3. Monotonicity: the count is nonincreasing in w' for w' > w
  4. The count at w' = w is a + 1 (same as below diagonal)
-/
import CausalAlgebraicGeometry.WidthTransitions3D
import Mathlib.Tactic

namespace WidthTransitionProps

open WidthTransitions3D

/-- Corollary 1a: transitions exist for w' ≤ w (count = a + 1 > 0). -/
theorem pos_count_below (a w w' : ℕ) (hw' : w' ≤ w) :
    0 < (validLowerBounds a w w').card := by
  rw [transition_count_below a w w' hw']
  omega

/-- Corollary 1b: transitions exist for w < w' ≤ a + w iff a + w ≥ w'. -/
theorem pos_count_above (a w w' : ℕ) (hw : w < w') (hb : w' ≤ a + w) (_ha : 0 < a) :
    0 < (validLowerBounds a w w').card := by
  rw [transition_count_above a w w' hw hb]
  omega

/-- Corollary 1c: no transitions for w' > a + w. -/
theorem no_transitions_beyond (a w w' : ℕ) (h : a + w < w') :
    (validLowerBounds a w w').card = 0 :=
  transition_count_zero a w w' h

/-- Corollary 2: the count is constant (= a+1) for all w' ≤ w. -/
theorem constant_below_diagonal (a w w₁ w₂ : ℕ) (h₁ : w₁ ≤ w) (h₂ : w₂ ≤ w) :
    (validLowerBounds a w w₁).card = (validLowerBounds a w w₂).card := by
  rw [transition_count_below a w w₁ h₁, transition_count_below a w w₂ h₂]

/-- Corollary 3: the count is strictly decreasing for w' > w.
    If w < w₁ < w₂ ≤ a + w, then count(w₂) < count(w₁). -/
theorem decreasing_above_diagonal (a w w₁ w₂ : ℕ)
    (hw₁ : w < w₁) (hw₂ : w₁ < w₂) (hb : w₂ ≤ a + w) :
    (validLowerBounds a w w₂).card < (validLowerBounds a w w₁).card := by
  rw [transition_count_above a w w₁ hw₁ (by omega),
      transition_count_above a w w₂ (by omega) hb]
  omega

/-- Corollary 4: the count drops by exactly 1 for each unit increase above w.
    count(w'+1) = count(w') - 1 for w < w' < a + w. -/
theorem unit_decrease (a w w' : ℕ) (hw : w < w') (hw' : w' < a + w) :
    (validLowerBounds a w w').card = (validLowerBounds a w (w' + 1)).card + 1 := by
  rw [transition_count_above a w w' hw (by omega),
      transition_count_above a w (w' + 1) (by omega) (by omega)]
  omega

/-- Corollary 5: the count at w' = 0 equals a + 1 (all centers valid). -/
theorem count_at_zero (a w : ℕ) :
    (validLowerBounds a w 0).card = a + 1 := by
  exact transition_count_below a w 0 (Nat.zero_le w)

/-- Corollary 6: the maximum target width is a + w.
    count(a + w) = 1 (only a' = 0 works). -/
theorem count_at_max (a w : ℕ) (ha : 0 < a ∨ 0 < w) :
    (validLowerBounds a w (a + w)).card = 1 := by
  by_cases hw : a + w ≤ w
  · -- a = 0
    have : a = 0 := by omega
    subst this
    simp [transition_count_below]
  · push_neg at hw
    rw [transition_count_above a w (a + w) (by omega) (le_refl _)]
    omega

end WidthTransitionProps
