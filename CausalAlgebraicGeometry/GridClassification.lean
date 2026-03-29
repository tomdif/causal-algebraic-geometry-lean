/-
  GridClassification.lean — Structural classification of order-convex subsets of product posets

  MAIN RESULT: A subset S ⊆ Fin m × Fin n is order-convex (in the product order)
  if and only if it satisfies the rectangle-fill property: for all (a₁,b₁), (a₂,b₂) ∈ S
  with a₁ ≤ a₂ and b₁ ≤ b₂, every (i,j) with a₁ ≤ i ≤ a₂ and b₁ ≤ j ≤ b₂ is in S.

  Corollaries: row fibers are intervals, column fibers are intervals.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

namespace CausalAlgebraicGeometry.GridClassification

variable {m n : ℕ}

/-! ## Definitions -/

/-- Component-wise partial order on Fin m × Fin n. -/
def GridLE (m n : ℕ) (a b : Fin m × Fin n) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2

instance : DecidableRel (GridLE m n) := fun a b =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- A subset S of Fin m × Fin n is order-convex if for all a, b ∈ S with a ≤ b,
    every c between a and b is also in S. -/
def IsGridConvex (m n : ℕ) (S : Finset (Fin m × Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, GridLE m n a b →
    ∀ c : Fin m × Fin n, GridLE m n a c → GridLE m n c b → c ∈ S

/-- The row fiber: the set of column indices j such that (i, j) ∈ S. -/
def RowFiber (m n : ℕ) (S : Finset (Fin m × Fin n)) (i : Fin m) : Finset (Fin n) :=
  S.image Prod.snd |>.filter (fun j => (i, j) ∈ S)

-- More direct definition that avoids going through image
lemma mem_rowFiber_iff {S : Finset (Fin m × Fin n)} {i : Fin m} {j : Fin n} :
    j ∈ RowFiber m n S i ↔ (i, j) ∈ S := by
  simp only [RowFiber, Finset.mem_filter, Finset.mem_image]
  constructor
  · exact fun ⟨_, h⟩ => h
  · intro h
    exact ⟨⟨(i, j), h, rfl⟩, h⟩

/-! ## Forward direction: convexity implies rectangle fill -/

/-- If S is grid-convex, then rectangles determined by comparable pairs in S are filled. -/
theorem rectangle_fill (S : Finset (Fin m × Fin n))
    (hS : IsGridConvex m n S)
    (a b : Fin m × Fin n)
    (ha : a ∈ S) (hb : b ∈ S)
    (hab : a.1 ≤ b.1 ∧ a.2 ≤ b.2) :
    ∀ (i : Fin m) (j : Fin n),
      a.1 ≤ i → i ≤ b.1 → a.2 ≤ j → j ≤ b.2 → (i, j) ∈ S := by
  intro i j hi1 hi2 hj1 hj2
  exact hS a ha b hb hab (i, j) ⟨hi1, hj1⟩ ⟨hi2, hj2⟩

/-- Row fibers of a grid-convex set are intervals. -/
theorem row_fiber_is_interval (S : Finset (Fin m × Fin n))
    (hS : IsGridConvex m n S) (i : Fin m)
    (j₁ j₂ : Fin n) (hj₁ : (i, j₁) ∈ S) (hj₂ : (i, j₂) ∈ S) (h : j₁ ≤ j₂) :
    ∀ j : Fin n, j₁ ≤ j → j ≤ j₂ → (i, j) ∈ S := by
  intro j hle1 hle2
  exact hS (i, j₁) hj₁ (i, j₂) hj₂ ⟨le_refl i, h⟩ (i, j) ⟨le_refl i, hle1⟩ ⟨le_refl i, hle2⟩

/-- Column fibers of a grid-convex set are intervals. -/
theorem column_fill (S : Finset (Fin m × Fin n))
    (hS : IsGridConvex m n S) (j : Fin n)
    (i₁ i₂ : Fin m) (hi₁ : (i₁, j) ∈ S) (hi₂ : (i₂, j) ∈ S) (h : i₁ ≤ i₂) :
    ∀ i : Fin m, i₁ ≤ i → i ≤ i₂ → (i, j) ∈ S := by
  intro i hle1 hle2
  exact hS (i₁, j) hi₁ (i₂, j) hi₂ ⟨h, le_refl j⟩ (i, j) ⟨hle1, le_refl j⟩ ⟨hle2, le_refl j⟩

/-! ## Backward direction: rectangle fill implies convexity -/

/-- The rectangle-fill property implies grid-convexity. -/
theorem profile_implies_convex (S : Finset (Fin m × Fin n))
    (h_rect : ∀ a ∈ S, ∀ b ∈ S, a.1 ≤ b.1 → a.2 ≤ b.2 →
      ∀ (i : Fin m) (j : Fin n),
        a.1 ≤ i → i ≤ b.1 → a.2 ≤ j → j ≤ b.2 → (i, j) ∈ S) :
    IsGridConvex m n S := by
  intro a ha b hb ⟨hab1, hab2⟩ c ⟨hac1, hac2⟩ ⟨hcb1, hcb2⟩
  exact h_rect a ha b hb hab1 hab2 c.1 c.2 hac1 hcb1 hac2 hcb2

/-! ## The main biconditional -/

/-- Grid-convexity is equivalent to the rectangle-fill property. -/
theorem grid_convex_iff_rectangle_fill (S : Finset (Fin m × Fin n)) :
    IsGridConvex m n S ↔
    ∀ a ∈ S, ∀ b ∈ S, a.1 ≤ b.1 → a.2 ≤ b.2 →
      ∀ (i : Fin m) (j : Fin n),
        a.1 ≤ i → i ≤ b.1 → a.2 ≤ j → j ≤ b.2 → (i, j) ∈ S := by
  constructor
  · intro hS a ha b hb hab1 hab2
    exact rectangle_fill S hS a b ha hb ⟨hab1, hab2⟩
  · exact profile_implies_convex S

/-! ## Row fiber interval characterization -/

/-- Grid-convexity implies row fibers are intervals (via RowFiber). -/
theorem row_fiber_interval_via_finset (S : Finset (Fin m × Fin n))
    (hS : IsGridConvex m n S) (i : Fin m)
    (j₁ j₂ : Fin n) (hj₁ : j₁ ∈ RowFiber m n S i) (hj₂ : j₂ ∈ RowFiber m n S i)
    (h : j₁ ≤ j₂) :
    ∀ j : Fin n, j₁ ≤ j → j ≤ j₂ → j ∈ RowFiber m n S i := by
  intro j hle1 hle2
  rw [mem_rowFiber_iff] at hj₁ hj₂ ⊢
  exact row_fiber_is_interval S hS i j₁ j₂ hj₁ hj₂ h j hle1 hle2

/-! ## Intermediate row activation -/

/-- If rows i₁ and i₂ are both active (nonempty fiber) in a grid-convex set with i₁ ≤ i₂,
    and there exist j₁ in row i₁ and j₂ in row i₂ with j₁ ≤ j₂, then every
    intermediate row k (i₁ ≤ k ≤ i₂) has both j₁ and j₂ in its fiber. -/
theorem intermediate_row_activation (S : Finset (Fin m × Fin n))
    (hS : IsGridConvex m n S)
    (i₁ i₂ : Fin m) (j₁ j₂ : Fin n)
    (h1 : (i₁, j₁) ∈ S) (h2 : (i₂, j₂) ∈ S)
    (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂)
    (k : Fin m) (hk1 : i₁ ≤ k) (hk2 : k ≤ i₂) :
    (k, j₁) ∈ S ∧ (k, j₂) ∈ S := by
  constructor
  · exact rectangle_fill S hS (i₁, j₁) (i₂, j₂) h1 h2 ⟨hi, hj⟩ k j₁ hk1 hk2 (le_refl j₁) hj
  · exact rectangle_fill S hS (i₁, j₁) (i₂, j₂) h1 h2 ⟨hi, hj⟩ k j₂ hk1 hk2 hj (le_refl j₂)

end CausalAlgebraicGeometry.GridClassification
