/-
  ConvexRect2xN.lean — Order-convex subsets of the product poset [2]×[n].

  The number of order-convex subsets of {0,1}×{0,...,n-1} under the
  componentwise partial order (i₁,j₁) ≤ (i₂,j₂) iff i₁ ≤ i₂ ∧ j₁ ≤ j₂.

  Verified values: a(1)=4, a(2)=13, a(3)=33, a(4)=71, a(5)=136, a(6)=239

  Conjectured polynomial:
    a(n) = (n⁴ + 4n³ + 17n² + 14n + 12) / 12

  Not yet in OEIS. Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Powerset

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace CausalAlgebraicGeometry.ConvexRect2xN

/-! ## Convexity on Fin m × Fin n with componentwise order -/

/-- Componentwise ≤ on Fin m × Fin n. -/
instance {m n : ℕ} : LE (Fin m × Fin n) :=
  ⟨fun a b => a.1 ≤ b.1 ∧ a.2 ≤ b.2⟩

instance {m n : ℕ} (a b : Fin m × Fin n) : Decidable (a ≤ b) :=
  show Decidable (a.1 ≤ b.1 ∧ a.2 ≤ b.2) from inferInstance

/-- A subset S of Fin m × Fin n is order-convex if whenever a, b ∈ S
    and a ≤ c ≤ b then c ∈ S. -/
def IsConvexRect (m n : ℕ) (S : Finset (Fin m × Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≤ b →
    ∀ c : Fin m × Fin n, a ≤ c → c ≤ b → c ∈ S

instance isConvexRectDec (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Decidable (IsConvexRect m n S) := by
  unfold IsConvexRect
  exact Finset.decidableDforallFinset

/-- Count of order-convex subsets of [m]×[n]. -/
def numConvexRect (m n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin n)).powerset.filter
    (fun S => decide (IsConvexRect m n S))).card

/-! ## Verified values for [2]×[n] -/

theorem rect2x1 : numConvexRect 2 1 = 4   := by native_decide
theorem rect2x2 : numConvexRect 2 2 = 13  := by native_decide
theorem rect2x3 : numConvexRect 2 3 = 33  := by native_decide
theorem rect2x4 : numConvexRect 2 4 = 71  := by native_decide
theorem rect2x5 : numConvexRect 2 5 = 136 := by native_decide
theorem rect2x6 : numConvexRect 2 6 = 239 := by native_decide

/-- All six values collected. -/
theorem convexRect2xN_values :
    numConvexRect 2 1 = 4
    ∧ numConvexRect 2 2 = 13
    ∧ numConvexRect 2 3 = 33
    ∧ numConvexRect 2 4 = 71
    ∧ numConvexRect 2 5 = 136
    ∧ numConvexRect 2 6 = 239 := by
  exact ⟨rect2x1, rect2x2, rect2x3, rect2x4, rect2x5, rect2x6⟩

/-!
## Conjectured formula (not proved here)

  a(n) = (n⁴ + 4n³ + 17n² + 14n + 12) / 12

Zero sorry. Zero custom axioms.
-/

end CausalAlgebraicGeometry.ConvexRect2xN
