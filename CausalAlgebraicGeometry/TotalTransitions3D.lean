/-
  Total Outgoing Transitions for the d=3 Width Chain

  From state (a, b) with width w = b - a + 1 ≥ 1:
  The total number of valid transitions (a', b') with a' ≤ a, b' ≤ b
  is exactly (a+1)(b+1) = (a+1)(a+w).

  From WidthTransitions3D, transitions to width w' have count:
    a + 1           for w' ≤ w  (w+1 such values: w' = 0,...,w)
    a + w - w' + 1  for w' = w+1,...,a+w  (a such values)

  Total = (w+1)(a+1) + Σ_{k=1}^{a} k = (w+1)(a+1) + a(a+1)/2

  But also total = (a+1)(a+w) since every (a',b') with a' ≤ a, b' ≤ b = a+w-1
  is a valid transition.

  We prove: (a+1)(b+1) = (a+1)(a+w) by connecting through the rectangle count.
-/
import CausalAlgebraicGeometry.WidthTransitions3D
import CausalAlgebraicGeometry.WidthKernel3D
import Mathlib.Tactic

namespace TotalTransitions3D

open WidthTransitions3D WidthKernel3D

/-- The total outgoing transitions from (a, b) = (a+1)(b+1). -/
theorem total_outgoing (a b : ℕ) :
    (zeroWidth a b).card + (posWidth a b).card = (a + 1) * (b + 1) :=
  kernel_normalization a b

/-- For a positive-width state with b = a + w - 1 (w ≥ 1):
    total = (a+1)(a+w). -/
theorem total_outgoing_width (a w : ℕ) (hw : 0 < w) :
    (zeroWidth a (a + w - 1)).card + (posWidth a (a + w - 1)).card =
    (a + 1) * (a + w) := by
  have hb : a + w - 1 + 1 = a + w := by omega
  rw [kernel_normalization, hb]

-- Verified: total counts match (a+1)(b+1) for small cases.
example : (zeroWidth 2 4).card + (posWidth 2 4).card = 3 * 5 := kernel_normalization 2 4
example : (zeroWidth 3 5).card + (posWidth 3 5).card = 4 * 6 := kernel_normalization 3 5
example : (zeroWidth 1 3).card + (posWidth 1 3).card = 2 * 4 := kernel_normalization 1 3
example : (zeroWidth 0 2).card + (posWidth 0 2).card = 1 * 3 := kernel_normalization 0 2

/-- The zero-width fraction for a square state (a = b) is
    the triangular number a(a+1)/2 out of (a+1)². -/
-- Verified instances:
-- These follow from the square case of the self-loop identity.
-- zeroWidth a a on [0,a]×[0,a] has |Z| = a(a+1)/2, so 2|Z| = a(a+1).
-- The general proof uses the same Gauss sum argument as SelfLoop3D.
example : 2 * (zeroWidth 3 3).card = 3 * 4 := by decide
example : 2 * (zeroWidth 4 4).card = 4 * 5 := by decide
example : 2 * (zeroWidth 5 5).card = 5 * 6 := by decide

-- When a = b (square), zero-width fraction = a(a+1)/(2(a+1)²) = a/(2(a+1)) → 1/2.
-- This connects to Theorem B: as a → ∞, P(w'=0) → 1/2 for "symmetric" states.

end TotalTransitions3D
