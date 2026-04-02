/-
  Continuum Kernel Scaling Limit (Theorem A, continuum version)

  The discrete transition count from WidthTransitions3D:
    count(w' ≤ w) = a + 1
    count(w' > w) = a + w - w' + 1
    total = (a+1)(a+w)

  Rescale: s = w/m, s' = w'/m, u = a/m. Then the transition DENSITY
  (count per unit s') in the continuum limit m → ∞ is:

    K(s, s') = (count at w' = s'm) / (total × (1/m))
             = m × count / total

  For s' ≤ s (below diagonal):
    count = um + 1 ≈ um, total ≈ (um)(um + sm) = u(u+s)m²
    density = m × um / (u(u+s)m²) = 1/(u+s)
    Averaged over u ∈ [0, 1-s]: K(s,s') = (1/(1-s)) ∫₀^{1-s} 1/(u+s) du
                                         = -ln(s)/(1-s)

  For s' > s (above diagonal):
    count = um + sm - s'm + 1 ≈ (u+s-s')m
    density = m × (u+s-s')m / (u(u+s)m²) = (u+s-s')/(u(u+s))
    Averaged over u: K(s,s') = [(s-s')ln((1-s)/(s'-s)) - s'ln(s')] / (s(1-s))

  For s' = 0 (collapse):
    P(0|s) = zeroWidth(a,b) / total
    In the continuum: P(0|s) = 1/2 + s·ln(s)/(2(1-s))

  This file states the discrete-to-continuum scaling as exact
  identities for the transition COUNT RATIOS at finite m.
-/
import CausalAlgebraicGeometry.WidthTransitions3D
import CausalAlgebraicGeometry.WidthKernel3D
import Mathlib.Tactic

namespace ContinuumKernel3D

open WidthTransitions3D WidthKernel3D

/-- The discrete transition probability from width w to width w' at center a
    is count/total = |validLowerBounds a w w'| / ((a+1)(a+w)).

    For w' ≤ w: this ratio is (a+1)/((a+1)(a+w)) = 1/(a+w).
    This is INDEPENDENT of w' (flat below diagonal). -/
theorem prob_below_flat (a w w₁ w₂ : ℕ) (hw : 0 < w) (h₁ : w₁ ≤ w) (h₂ : w₂ ≤ w) :
    (validLowerBounds a w w₁).card * (a + w) =
    (validLowerBounds a w w₂).card * (a + w) := by
  rw [transition_count_below a w w₁ h₁, transition_count_below a w w₂ h₂]

/-- The ratio below diagonal: count × m / total → 1/(u+s) as m → ∞.
    Discrete version: count(w') = a+1, total = (a+1)(a+w).
    So count/total = 1/(a+w) = 1/b+1 where b = a+w-1. -/
theorem ratio_below (a w w' : ℕ) (hw' : w' ≤ w) :
    (validLowerBounds a w w').card = a + 1 :=
  transition_count_below a w w' hw'

/-- The ratio above diagonal decreases linearly.
    count(w') = a+w-w'+1, so count/total = (a+w-w'+1)/((a+1)(a+w)). -/
theorem ratio_above (a w w' : ℕ) (hw : w < w') (hb : w' ≤ a + w) :
    (validLowerBounds a w w').card = a + w - w' + 1 :=
  transition_count_above a w w' hw hb

/-- The flat-below-diagonal property is the discrete precursor of
    K(s,s') = -ln(s)/(1-s) for s' ≤ s. It says:
    the transition density to any width ≤ current width is CONSTANT. -/
theorem flat_below (a w : ℕ) (hw : 0 < w) :
    ∀ w₁ w₂, w₁ ≤ w → w₂ ≤ w →
    (validLowerBounds a w w₁).card = (validLowerBounds a w w₂).card := by
  intro w₁ w₂ h₁ h₂
  rw [transition_count_below a w w₁ h₁, transition_count_below a w w₂ h₂]

/-- The linear-above-diagonal property is the discrete precursor of
    the decaying kernel for s' > s. The count decreases by 1 per unit. -/
theorem linear_above (a w w' : ℕ) (hw : w < w') (hb : w' + 1 ≤ a + w) :
    (validLowerBounds a w w').card = (validLowerBounds a w (w' + 1)).card + 1 := by
  rw [transition_count_above a w w' hw (by omega),
      transition_count_above a w (w' + 1) (by omega) hb]
  omega

-- Connecting the flat+linear structure to the continuum kernel:
-- In the continuum limit (m → ∞, s = w/m, s' = w'/m, u = a/m):
--   Below diagonal: density = 1/(u+s) → averaged: -ln(s)/(1-s)
--   Above diagonal: density = (u+s-s')/(u(u+s)) → averaged: see formula
--   Collapse: P(0|s) = zeroWidth/(total) → 1/2 + s ln(s)/(2(1-s))
-- These are verified numerically to 10⁻⁹ in scripts/gap_d3_fast.py.
-- The proofs above establish the discrete precursors exactly.
-- Continuum formulas (verified numerically, not formalized in Lean real analysis):
-- K(s,s') = -ln(s)/(1-s) for 0 < s' ≤ s
-- K(s,s') = [(s-s')ln((1-s)/(s'-s)) - s'ln(s')] / (s(1-s)) for s' > s
-- P(0|s) = 1/2 + s·ln(s)/(2(1-s))

end ContinuumKernel3D
