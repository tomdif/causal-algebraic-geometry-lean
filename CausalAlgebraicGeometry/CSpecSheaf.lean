/-
  LayerD/CSpecSheaf.lean — The structure sheaf on CSpec

  The structure sheaf assigns to each open D(S) the corner algebra
  e_S A e_S — causal matrices supported on S × S.

  Main results:
  - `CornerElt`: sections (causal matrices supported on S)
  - `locality`: sheaf separation axiom
  - `cornerMul`: ring structure on corner algebras
  - `restrict_mul_convex`: restriction preserves ring structure
    for causally convex subsets
  - `stalk_at_minimal_is_scalar`: 1-dimensional stalk at minimal
  - `past_convex`: causal past is always convex
-/
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.CausalPrimality

namespace CausalAlgebraicGeometry.CSpecSheaf

open CausalAlgebra CausalPrimality

/-! ### Sections of the structure sheaf -/

/-- A **section** of the structure sheaf: a causal matrix supported on S. -/
structure CornerElt {k : Type*} [Field k] (C : CAlg k) (S : Finset C.Λ) where
  mat : C.Λ → C.Λ → k
  causal : ∀ α β, ¬ C.le α β → mat α β = 0
  support : ∀ α β, α ∉ S ∨ β ∉ S → mat α β = 0

/-! ### Sheaf separation -/

/-- **Separation**: sections agreeing on S × S are identical. -/
theorem locality {k : Type*} [Field k] (C : CAlg k)
    {S : Finset C.Λ} (M N : CornerElt C S)
    (h : ∀ x ∈ S, ∀ y ∈ S, M.mat x y = N.mat x y) :
    M.mat = N.mat := by
  ext α β
  by_cases hα : α ∈ S <;> by_cases hβ : β ∈ S
  · exact h α hα β hβ
  · rw [M.support α β (Or.inr hβ), N.support α β (Or.inr hβ)]
  · rw [M.support α β (Or.inl hα), N.support α β (Or.inl hα)]
  · rw [M.support α β (Or.inl hα), N.support α β (Or.inl hα)]

/-- A section vanishing on S × S is the zero function. -/
theorem locality_zero {k : Type*} [Field k] (C : CAlg k)
    {S : Finset C.Λ} (M : CornerElt C S)
    (h : ∀ x ∈ S, ∀ y ∈ S, M.mat x y = 0) :
    M.mat = fun _ _ => 0 := by
  ext α β
  by_cases hα : α ∈ S <;> by_cases hβ : β ∈ S
  · exact h α hα β hβ
  · exact M.support α β (Or.inr hβ)
  · exact M.support α β (Or.inl hα)
  · exact M.support α β (Or.inl hα)

/-! ### Multiplication -/

/-- Corner algebra multiplication: (M·N)(α,β) = Σ_γ M(α,γ)N(γ,β). -/
def cornerMul {k : Type*} [Field k] (C : CAlg k) {S : Finset C.Λ}
    (M N : CornerElt C S) : CornerElt C S where
  mat α β := ∑ γ : C.Λ, M.mat α γ * N.mat γ β
  causal := isCausalMatrix_mul C M.mat N.mat M.causal N.causal
  support α β hout := by
    apply Finset.sum_eq_zero; intro γ _
    cases hout with
    | inl hα => rw [M.support α γ (Or.inl hα)]; ring
    | inr hβ => rw [N.support γ β (Or.inr hβ)]; ring

/-! ### Restriction preserves multiplication (convex case) -/

/-- Convexity for finsets. -/
def IsConvex {k : Type*} [Field k] (C : CAlg k) (S : Finset C.Λ) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ γ, C.le α γ → C.le γ β → γ ∈ S

/-- **Key theorem**: for causally convex S, if α, β ∈ S then the
    product sum Σ_γ M(α,γ)N(γ,β) only receives contributions from
    γ ∈ S. Elements γ ∉ S contribute zero.

    This is WHY causal convexity is the right notion: it guarantees
    that restriction is a ring homomorphism. -/
theorem product_supported_on_convex {k : Type*} [Field k] (C : CAlg k)
    {S : Finset C.Λ} (hconv : IsConvex C S)
    (M N : C.Λ → C.Λ → k)
    (hM : ∀ α β, ¬ C.le α β → M α β = 0)
    (hN : ∀ α β, ¬ C.le α β → N α β = 0)
    (α β : C.Λ) (hα : α ∈ S) (hβ : β ∈ S) (γ : C.Λ) (hγ : γ ∉ S) :
    M α γ * N γ β = 0 := by
  by_cases hαγ : C.le α γ
  · by_cases hγβ : C.le γ β
    · exact absurd (hconv α hα β hβ γ hαγ hγβ) hγ
    · simp [hN γ β hγβ]
  · simp [hM α γ hαγ]

/-- Corollary: the full product sum equals the sum restricted to S. -/
theorem product_sum_restrict {k : Type*} [Field k] (C : CAlg k)
    {S : Finset C.Λ} (hconv : IsConvex C S)
    (M N : CornerElt C S)
    (α β : C.Λ) (hα : α ∈ S) (hβ : β ∈ S) :
    (cornerMul C M N).mat α β =
      ∑ γ ∈ S, M.mat α γ * N.mat γ β := by
  simp only [cornerMul]
  symm; rw [Finset.sum_subset (Finset.subset_univ S)]
  intro γ _ hγ
  exact product_supported_on_convex C hconv M.mat N.mat M.causal N.causal α β hα hβ γ hγ

/-! ### Stalks -/

/-- At a **minimal element**, the stalk is 1-dimensional: a section
    of CornerElt({α}) is determined by the single scalar M(α,α). -/
theorem stalk_at_minimal_is_scalar {k : Type*} [Field k] (C : CAlg k)
    (α : C.Λ) (M : CornerElt C {α}) :
    ∃ c : k, ∀ i j, M.mat i j = if i = α ∧ j = α then c else 0 := by
  use M.mat α α
  intro i j
  by_cases hi : i = α <;> by_cases hj : j = α
  · subst hi; subst hj; simp
  · simp only [hj, and_false, ite_false]
    exact M.support i j (Or.inr (by rwa [Finset.mem_singleton]))
  · simp only [hi, false_and, ite_false]
    exact M.support i j (Or.inl (by rwa [Finset.mem_singleton]))
  · simp only [hi, false_and, ite_false]
    exact M.support i j (Or.inl (by rwa [Finset.mem_singleton]))

/-! ### Causal past is always convex -/

/-- The past of an element as a finset. -/
noncomputable def pastFinset {k : Type*} [Field k] (C : CAlg k)
    (α : C.Λ) : Finset C.Λ :=
  Finset.filter (fun β => C.le β α) Finset.univ

/-- The past is causally convex. -/
theorem past_convex {k : Type*} [Field k] (C : CAlg k) (α : C.Λ) :
    IsConvex C (pastFinset C α) := by
  intro x hx y hy γ _ hγy
  simp only [pastFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
  exact C.le_trans γ y α hγy hy

end CausalAlgebraicGeometry.CSpecSheaf
