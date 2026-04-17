/-
  ConvexRect3xN.lean — Order-convex subsets of the product poset [3]×[n].

  The number of order-convex subsets of {0,1,2}×{0,...,n-1} under the
  componentwise partial order (i₁,j₁) ≤ (i₂,j₂) iff i₁ ≤ i₂ ∧ j₁ ≤ j₂.

  Verified values: a(1)=7, a(2)=33, a(3)=114, a(4)=321

  Conjectured polynomial:
    a(n) = (n⁶ + 9n⁵ + 61n⁴ + 159n³ + 370n² + 264n + 144) / 144

  Not yet in OEIS. Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Powerset

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 3200000

namespace CausalAlgebraicGeometry.ConvexRect3xN

/-! ## Convexity on Fin m × Fin n with componentwise order -/

instance {m n : ℕ} : LE (Fin m × Fin n) :=
  ⟨fun a b => a.1 ≤ b.1 ∧ a.2 ≤ b.2⟩

instance {m n : ℕ} (a b : Fin m × Fin n) : Decidable (a ≤ b) :=
  show Decidable (a.1 ≤ b.1 ∧ a.2 ≤ b.2) from inferInstance

def IsConvexRect (m n : ℕ) (S : Finset (Fin m × Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≤ b →
    ∀ c : Fin m × Fin n, a ≤ c → c ≤ b → c ∈ S

instance isConvexRectDec (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Decidable (IsConvexRect m n S) := by
  unfold IsConvexRect
  exact Finset.decidableDforallFinset

def numConvexRect (m n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin n)).powerset.filter
    (fun S => decide (IsConvexRect m n S))).card

/-! ## Verified values for [3]×[n] -/

theorem rect3x1 : numConvexRect 3 1 = 7   := by native_decide
theorem rect3x2 : numConvexRect 3 2 = 33  := by native_decide
theorem rect3x3 : numConvexRect 3 3 = 114 := by native_decide
theorem rect3x4 : numConvexRect 3 4 = 321 := by native_decide

/-- All four values collected. -/
theorem convexRect3xN_values :
    numConvexRect 3 1 = 7
    ∧ numConvexRect 3 2 = 33
    ∧ numConvexRect 3 3 = 114
    ∧ numConvexRect 3 4 = 321 := by
  exact ⟨rect3x1, rect3x2, rect3x3, rect3x4⟩

/-!
## Conjectured formula (not proved here)

  a(n) = (n⁶ + 9n⁵ + 61n⁴ + 159n³ + 370n² + 264n + 144) / 144

Zero sorry. Zero custom axioms.
-/

end CausalAlgebraicGeometry.ConvexRect3xN
