/-
  EulerCharacteristic.lean — S_BD is the Euler characteristic of the Hasse diagram.

  The Benincasa-Dowker action S_BD(S) = |S| - |links(S)| equals the Euler
  characteristic χ = |V| - |E| of the Hasse diagram of S (the covering relation
  graph restricted to the convex subset).

  The positive energy theorem (BDAction.lean) then becomes:
    χ(Hasse(S)) ≥ χ(Hasse([m]×[n]))
  for all nonempty convex S, with equality iff S = [m]×[n].

  This is a DISCRETE GAUSS-BONNET EXTREMALITY PRINCIPLE:
  flat spacetime (the full grid) uniquely minimizes the Euler characteristic
  of the Hasse diagram among all convex sub-diagrams.

  The renormalized action S_BD^ren = χ(S) - χ(flat) ≥ 0 measures "curvature":
  how far S is from the flat configuration, in exact analogy to ∫R√g.

  Zero sorry.
-/
import CausalAlgebraicGeometry.BDAction

namespace CausalAlgebraicGeometry.EulerCharacteristic

open CausalAlgebraicGeometry.BDAction
open CausalAlgebraicGeometry.GridClassification

/-- The Euler characteristic of the Hasse diagram: χ = |V| - |E|. -/
def eulerChar (m n : ℕ) (S : Finset (Fin m × Fin n)) : Int :=
  (S.card : Int) - (numLinks m n S : Int)

/-- S_BD = χ(Hasse) by definition. -/
theorem bd_eq_euler (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    bdAction m n S = eulerChar m n S := by
  rfl

/-- The positive energy theorem restated: χ(Hasse(S)) ≥ -(m-1)(n-1) + 1. -/
theorem euler_char_ge {m n : ℕ} {S : Finset (Fin m × Fin n)}
    (hS : IsGridConvex m n S) (hne : S.Nonempty) :
    eulerChar m n S ≥ -((m : Int) - 1) * ((n : Int) - 1) + 1 := by
  rw [← bd_eq_euler]; exact bd_action_ge hS hne

/-- χ([m]×[n]) = -(m-1)(n-1) + 1 (the "flat space Euler characteristic"). -/
theorem euler_char_fullGrid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    eulerChar m n (fullGrid m n) = -((m : Int) - 1) * ((n : Int) - 1) + 1 := by
  rw [← bd_eq_euler]; exact bd_action_fullGrid m n hm hn

/-- Kernel verification: χ([2]²) = 0, χ([3]²) = -3, χ([4]²) = -8. -/
theorem euler_2 : eulerChar 2 2 (fullGrid 2 2) = 0 := by native_decide
theorem euler_3 : eulerChar 3 3 (fullGrid 3 3) = -3 := by native_decide
theorem euler_4 : eulerChar 4 4 (fullGrid 4 4) = -8 := by native_decide

/-! ## The discrete Gauss-Bonnet interpretation

  In 2D continuum Riemannian geometry:
    ∫_M R dA = 2π χ(M)     (Gauss-Bonnet)

  In the discrete framework:
    S_BD(S) = χ(Hasse(S))   (by definition)

  The positive energy theorem:
    χ(S) ≥ χ(flat)           (flat = unique minimum)

  The renormalized "curvature action":
    S_BD^ren(S) = χ(S) - χ(flat) ≥ 0   (≥ 0, = 0 iff flat)

  This is a discrete analogue of the variational principle:
    ∫ R √g dA ≥ ∫ R_flat √g dA = 0   (flat space has R = 0)

  The Euler characteristic provides the bridge between the combinatorial
  action (element count minus link count) and differential geometry
  (integrated curvature). The positive energy theorem is the discrete
  Gauss-Bonnet extremality principle.
-/

end CausalAlgebraicGeometry.EulerCharacteristic
