/-
  CausalAlgebraicGeometry/SlabGauge.lean — Gauge structure of the slab representation

  The slab theorem says every convex subset of [m]^{d+1} is a slab between
  antitone boundaries. The CHOICE of which coordinate is "height" is a gauge
  freedom: the geometric content (area, spectral gap) is independent of this
  choice.

  Main results:
  1. `slabWidth`, `totalArea`: basic slab measurement
  2. `area_invariant_swap`: |S| = |S^T| for coordinate transposition
  3. `gamma_gauge_invariant`: comparability is preserved under coordinate
     permutations (hence spectral gap is gauge-invariant)

  Zero sorry.
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Logic.Equiv.Defs

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.SlabGauge

/-! ## Slab width and total area -/

/-- The width of a slab at a single position: if a ≤ b then b - a + 1, else 0. -/
def slabWidth (a b : ℕ) : ℕ := if a ≤ b then b - a + 1 else 0

/-- Total area (volume) of a slab defined by lower boundary `a` and upper boundary `b`. -/
def totalArea (m : ℕ) (a b : Fin m → ℕ) : ℕ :=
  Finset.univ.sum (fun j => slabWidth (a j) (b j))

/-- slabWidth is zero when a > b. -/
theorem slabWidth_of_gt {a b : ℕ} (h : b < a) : slabWidth a b = 0 := by
  simp [slabWidth, Nat.not_le.mpr h]

/-- slabWidth when a ≤ b gives b - a + 1. -/
theorem slabWidth_of_le {a b : ℕ} (h : a ≤ b) : slabWidth a b = b - a + 1 := by
  simp [slabWidth, h]

/-! ## Coordinate transposition for 2D subsets -/

/-- Swap the two coordinates of a point in [m]^2. -/
def swap2 (m : ℕ) (p : Fin 2 → Fin m) : Fin 2 → Fin m :=
  fun i => p (Equiv.swap (0 : Fin 2) 1 i)

/-- swap2 is its own inverse. -/
theorem swap2_involutive (m : ℕ) : Function.Involutive (swap2 m) := by
  intro p
  ext i
  simp [swap2, Equiv.swap_apply_self]

/-- swap2 is injective (since it is involutive). -/
theorem swap2_injective (m : ℕ) : Function.Injective (swap2 m) :=
  (swap2_involutive m).injective

/-- The transpose of a finite subset S ⊂ [m]^2. -/
def transposeSet (m : ℕ) (S : Finset (Fin 2 → Fin m)) : Finset (Fin 2 → Fin m) :=
  S.image (swap2 m)

/-- **Area invariance under transposition**: |S| = |S^T|.
    The area of a convex set does not depend on which coordinate we call "height". -/
theorem area_invariant_swap (m : ℕ) (S : Finset (Fin 2 → Fin m)) :
    (transposeSet m S).card = S.card := by
  exact Finset.card_image_of_injective S (swap2_injective m)

/-! ## Comparability and coordinate permutations -/

/-- Two points are comparable in the product order if one dominates the other
    coordinatewise. -/
def comparable {n m : ℕ} (P Q : Fin n → Fin m) : Prop :=
  (∀ i, P i ≤ Q i) ∨ (∀ i, Q i ≤ P i)

/-- Permuting coordinates preserves the componentwise order. -/
theorem le_iff_perm_le {n m : ℕ} (σ : Equiv.Perm (Fin n)) (P Q : Fin n → Fin m) :
    (∀ i, P i ≤ Q i) ↔ (∀ i, P (σ.symm i) ≤ Q (σ.symm i)) := by
  constructor
  · intro h i; exact h (σ.symm i)
  · intro h i
    have := h (σ i)
    simp at this
    exact this

/-- **Gauge invariance of comparability**: comparable(P,Q) iff comparable(σP, σQ)
    for any coordinate permutation σ. This is because permuting coordinates
    preserves the product order. -/
theorem gamma_gauge_invariant {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (P Q : Fin n → Fin m) :
    comparable P Q ↔ comparable (P ∘ σ.symm) (Q ∘ σ.symm) := by
  simp only [comparable, Function.comp]
  constructor
  · rintro (h | h)
    · left; intro i; exact h (σ.symm i)
    · right; intro i; exact h (σ.symm i)
  · rintro (h | h)
    · left; intro i
      have := h (σ i)
      simp at this
      exact this
    · right; intro i
      have := h (σ i)
      simp at this
      exact this

/-! ## Consequences -/

/-- The transpose of the transpose is the original set. -/
theorem transposeSet_involutive (m : ℕ) (S : Finset (Fin 2 → Fin m)) :
    transposeSet m (transposeSet m S) = S := by
  simp only [transposeSet]
  rw [Finset.image_image]
  have : swap2 m ∘ swap2 m = id := by
    ext p i
    simp [Function.comp, swap2_involutive m p]
  rw [this, Finset.image_id]

/-- A point is in S iff its swap is in S^T. -/
theorem mem_transposeSet_iff (m : ℕ) (S : Finset (Fin 2 → Fin m))
    (p : Fin 2 → Fin m) :
    swap2 m p ∈ transposeSet m S ↔ p ∈ S := by
  simp only [transposeSet, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    have : p = q := by
      have h2 : swap2 m (swap2 m q) = q := swap2_involutive m q
      have h3 : swap2 m (swap2 m p) = p := swap2_involutive m p
      rw [← h3, ← heq, h2]
    rw [this]
    exact hq
  · intro hp
    exact ⟨p, hp, rfl⟩

end CausalAlgebraicGeometry.SlabGauge
