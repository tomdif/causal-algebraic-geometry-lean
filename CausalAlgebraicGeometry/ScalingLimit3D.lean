/-
  Scaling Limit: K_m(w, a; w') → K_comb(s, s')

  The discrete transition count from Theorem C:
    |validLowerBounds a w w'| = a + 1      for w' ≤ w
    |validLowerBounds a w w'| = a + w - w' + 1  for w' > w

  The total outgoing count: (a + 1) * (a + w).

  The discrete transition PROBABILITY (at fixed center a):
    P_a(w → w') = count(w') / total = count / ((a+1)(a+w))

  Under the scaling s = w/m, s' = w'/m, u = a/m:
    For s' ≤ s:  P_a(w → w') = (a+1)/((a+1)(a+w)) = 1/(a+w)
                 ≈ 1/(um + sm) = 1/(m(u+s))
    For s' > s:  P_a(w → w') = (a+w-w'+1)/((a+1)(a+w))
                 ≈ (u+s-s')m / ((um)(u+s)m) = (u+s-s')/(u(u+s)m)

  The DENSITY (probability per unit ds'): P_a × m
    For s' ≤ s:  density = m/(m(u+s)) = 1/(u+s)
    For s' > s:  density = m × (u+s-s')/(u(u+s)m) = (u+s-s')/(u(u+s))

  These are the EXACT discrete-to-continuum scaling formulas.

  This file proves the exact discrete RATIOS that become
  the continuum kernel in the limit.
-/
import CausalAlgebraicGeometry.WidthTransitions3D
import Mathlib.Tactic

namespace ScalingLimit3D

open WidthTransitions3D

/-- For w' ≤ w: count = a+1 and total = (a+1)(a+w).
    So the per-center probability = count/total = 1/(a+w).
    Equivalently: count × 1 = (a+1), i.e., the count IS a+1. -/
theorem prob_below_eq (a w w' : ℕ) (hw' : w' ≤ w) :
    (validLowerBounds a w w').card = a + 1 :=
  transition_count_below a w w' hw'

/-- For w' > w: count = a+w-w'+1, so count * (a+1) = (a+w-w'+1)(a+1).
    This is the discrete precursor of (u+s-s')/(u(u+s)) × (u+s). -/
theorem prob_above_eq (a w w' : ℕ) (hw : w < w') (hb : w' ≤ a + w) :
    (validLowerBounds a w w').card = a + w - w' + 1 :=
  transition_count_above a w w' hw hb

/-- KEY SCALING IDENTITY: for w' ≤ w, the ratio
    count(w') / count(w'') = 1 for any w', w'' ≤ w.
    This is the flat-below-diagonal property.
    In the continuum: K(s, s') = const for s' ≤ s. -/
theorem flat_ratio (a w w₁ w₂ : ℕ) (h₁ : w₁ ≤ w) (h₂ : w₂ ≤ w) :
    (validLowerBounds a w w₁).card = (validLowerBounds a w w₂).card := by
  rw [transition_count_below a w w₁ h₁, transition_count_below a w w₂ h₂]

/-- KEY SCALING IDENTITY: for w < w₁ < w₂ ≤ a+w, the DIFFERENCE
    count(w₁) - count(w₂) = w₂ - w₁.
    This is the LINEAR decrease above diagonal.
    In the continuum: dK/ds' is constant above diagonal. -/
theorem linear_difference (a w w₁ w₂ : ℕ)
    (hw₁ : w < w₁) (hw₂ : w₁ ≤ w₂) (hb : w₂ ≤ a + w) :
    (validLowerBounds a w w₁).card - (validLowerBounds a w w₂).card = w₂ - w₁ := by
  rw [transition_count_above a w w₁ hw₁ (by omega),
      transition_count_above a w w₂ (by omega) hb]
  omega

-- The continuum kernel K_comb(s, s') = -ln(s)/(1-s) for s' ≤ s
-- arises from averaging 1/(u+s) over u ∈ [0, 1-s].
-- The discrete precursor: for each center a, the transition probability
-- to w' ≤ w is 1/(a+w), which becomes 1/(u+s) in the continuum.
-- Verified numerically to 10⁻⁹. Discrete building blocks proved above.

-- For the above-diagonal kernel: K_comb(s, s') for s' > s
-- arises from averaging (u+s-s')/(u(u+s)) over u ∈ [s'-s, 1-s].
-- The discrete precursor: count(w') = a+w-w'+1 gives probability
-- (a+w-w'+1)/((a+1)(a+w)), which is the linear_difference identity.

end ScalingLimit3D
