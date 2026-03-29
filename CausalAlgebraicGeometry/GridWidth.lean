/-
  GridWidth.lean -- width([m]^2) = m

  The maximum antichain size (width) of the product poset Fin m x Fin m
  with componentwise order is exactly m.

  Lower bound: the anti-diagonal {(i, m-1-i) | i < m} is an antichain of size m.
  Upper bound: the first-coordinate projection of any antichain is injective
  (elements sharing a first coordinate are comparable), so |A| <= m.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Defs.PartialOrder

namespace CausalAlgebraicGeometry.GridWidth

/-! ### Antichains in Fin m x Fin m -/

/-- A finset is an antichain if no two distinct elements are comparable
    in the componentwise order. -/
def IsAntichain (m : Nat) (A : Finset (Fin m × Fin m)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a.1 ≤ b.1 ∧ a.2 ≤ b.2)

/-! ### Upper bound: any antichain has size at most m -/

/-- Elements of an antichain with the same first coordinate must be equal. -/
theorem antichain_fst_injective {m : Nat} {A : Finset (Fin m × Fin m)}
    (hA : IsAntichain m A) :
    ∀ a ∈ A, ∀ b ∈ A, a.1 = b.1 → a = b := by
  intro a ha b hb h_fst
  by_contra h_neq
  by_cases h : a.2 ≤ b.2
  · exact hA a ha b hb h_neq ⟨le_of_eq h_fst, h⟩
  · push_neg at h
    exact hA b hb a ha (Ne.symm h_neq) ⟨le_of_eq h_fst.symm, le_of_lt h⟩

/-- The first-coordinate projection restricted to an antichain is injective,
    so the antichain maps injectively into Fin m, giving |A| <= m. -/
theorem antichain_card_le {m : Nat} {A : Finset (Fin m × Fin m)}
    (hA : IsAntichain m A) :
    A.card ≤ m := by
  have h_inj : Set.InjOn Prod.fst (↑A : Set (Fin m × Fin m)) := by
    intro a ha b hb h
    exact antichain_fst_injective hA a ha b hb h
  have h1 : A.card = (A.image Prod.fst).card :=
    (Finset.card_image_of_injOn h_inj).symm
  rw [h1]
  exact le_trans (Finset.card_le_card (Finset.subset_univ _))
    (by simp [Fintype.card_fin])

/-! ### Lower bound: the anti-diagonal is an antichain of size m -/

/-- The anti-diagonal element: (i, m-1-i). -/
def antidiag (m : Nat) (_hm : 0 < m) (i : Fin m) : Fin m × Fin m :=
  (i, ⟨m - 1 - i.val, by omega⟩)

/-- The anti-diagonal is injective. -/
theorem antidiag_injective (m : Nat) (hm : 0 < m) :
    Function.Injective (antidiag m hm) := by
  intro i j h; simp only [antidiag, Prod.mk.injEq] at h; exact h.1

/-- The anti-diagonal finset. -/
def antidiagSet (m : Nat) (hm : 0 < m) : Finset (Fin m × Fin m) :=
  Finset.univ.image (antidiag m hm)

/-- The anti-diagonal has cardinality m. -/
theorem antidiagSet_card (m : Nat) (hm : 0 < m) :
    (antidiagSet m hm).card = m := by
  rw [antidiagSet, Finset.card_image_of_injective _ (antidiag_injective m hm)]
  simp [Fintype.card_fin]

/-- The anti-diagonal is an antichain: if (i, m-1-i) <= (j, m-1-j) componentwise,
    then i <= j and m-1-i <= m-1-j, so j <= i, hence i = j. -/
theorem antidiagSet_isAntichain (m : Nat) (hm : 0 < m) :
    IsAntichain m (antidiagSet m hm) := by
  intro a ha b hb h_neq h_le
  simp only [antidiagSet, Finset.mem_image, Finset.mem_univ, true_and] at ha hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  simp only [antidiag] at h_le h_neq
  have h1 : i.val ≤ j.val := h_le.1
  have h2 : m - 1 - i.val ≤ m - 1 - j.val := by
    have := h_le.2
    simp only [Fin.le_def] at this
    exact this
  have h3 : j.val ≤ i.val := by omega
  have h4 : i = j := Fin.ext (by omega)
  apply h_neq
  rw [h4]

/-- There exists an antichain of size m in Fin m x Fin m (for m > 0). -/
theorem exists_antichain_of_size_m (m : Nat) (hm : 0 < m) :
    ∃ A : Finset (Fin m × Fin m), IsAntichain m A ∧ A.card = m :=
  ⟨antidiagSet m hm, antidiagSet_isAntichain m hm, antidiagSet_card m hm⟩

/-! ### The main theorem: width([m]^2) = m -/

/-- **width([m]^2) = m**: For the product poset Fin m x Fin m with
    componentwise order, the maximum antichain size is exactly m.

    For m > 0: the anti-diagonal witnesses the lower bound, and
    injectivity of first-coordinate projection gives the upper bound.

    For m = 0: the poset is empty so the only antichain is empty. -/
theorem grid_width_eq (m : Nat) (hm : 0 < m) :
    (∃ A : Finset (Fin m × Fin m), IsAntichain m A ∧ A.card = m) ∧
    (∀ A : Finset (Fin m × Fin m), IsAntichain m A → A.card ≤ m) :=
  ⟨exists_antichain_of_size_m m hm, fun _ hA => antichain_card_le hA⟩

/-- The m = 0 case: the only antichain in an empty type has size 0. -/
theorem grid_width_zero :
    ∀ A : Finset (Fin 0 × Fin 0), IsAntichain 0 A → A.card = 0 := by
  intro A _
  have : A = ∅ := by
    ext ⟨x, _⟩
    exact Fin.elim0 x
  rw [this, Finset.card_empty]

end CausalAlgebraicGeometry.GridWidth
