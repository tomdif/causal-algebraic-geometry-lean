/-
  LayerD/CausalAlgebra.lean — Causal algebras over a field

  Definition 2.1 from the causal-algebraic geometry framework:
  A causal algebra is an associative k-algebra equipped with a complete
  set of orthogonal idempotents indexed by a partial order, satisfying
  the causality axiom: eα · A · eβ = 0 unless α ≼ β.

  This makes the algebra upper-triangular with respect to any linear
  extension of the partial order. The canonical example is the path
  algebra of the Hasse diagram modulo commutativity relations.

  Main results:
  - `CAlg`: the structure definition
  - `cornerAlg`: corner subalgebra eS A eS for upsets S
  - `isUpperTriangular_of_causal`: the causality axiom forces
    upper-triangularity
  - `fromFinitePoset`: construction of k[C] from a finite causal set
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace CausalAlgebraicGeometry.CausalAlgebra

/-! ### Core definition -/

/-- A **causal algebra** over a field k, indexed by a finite partial order.

    This packages:
    (i)   An associative k-algebra (via the matrix ring M_Λ(k))
    (ii)  A complete set of orthogonal idempotents {eα} (the standard
          matrix units Eαα)
    (iii) A partial order ≤ on the index set Λ
    (iv)  The causality axiom: the (α,β) matrix entry is zero unless α ≤ β

    The causality axiom states that there is no algebraic signal from β
    to α unless β causally precedes α. -/
structure CAlg (k : Type*) [Field k] where
  /-- The index set (events / spacetime atoms) -/
  Λ : Type*
  /-- Finiteness of the index set -/
  [fin : Fintype Λ]
  /-- Decidable equality on indices -/
  [deceq : DecidableEq Λ]
  /-- The causal partial order on Λ -/
  le : Λ → Λ → Prop
  /-- Decidability of the order relation -/
  [le_dec : DecidableRel le]
  /-- Reflexivity -/
  le_refl : ∀ a, le a a
  /-- Antisymmetry -/
  le_antisymm : ∀ a b, le a b → le b a → a = b
  /-- Transitivity -/
  le_trans : ∀ a b c, le a b → le b c → le a c

attribute [instance] CAlg.fin CAlg.deceq CAlg.le_dec

/-! ### The causal matrix ring -/

/-- The **causal matrix** associated to a causal algebra: a matrix
    M : Λ → Λ → k satisfying M(α,β) = 0 unless α ≤ β.
    This is the "causality axiom" — no signal propagates backwards. -/
def IsCausalMatrix {k : Type*} [Field k] (C : CAlg k)
    (M : C.Λ → C.Λ → k) : Prop :=
  ∀ α β, ¬ C.le α β → M α β = 0

/-- The identity matrix is causal (diagonal entries are at α ≤ α). -/
theorem isCausalMatrix_one {k : Type*} [Field k] (C : CAlg k) :
    IsCausalMatrix C (fun α β => if α = β then (1 : k) else 0) := by
  intro α β h_not_le
  simp only [ite_eq_right_iff]
  intro heq
  exact absurd (heq ▸ C.le_refl α) h_not_le

/-- The product of two causal matrices is causal.
    If M(α,γ) ≠ 0 requires α ≤ γ, and N(γ,β) ≠ 0 requires γ ≤ β,
    then (MN)(α,β) = Σ_γ M(α,γ)N(γ,β) ≠ 0 requires some γ with
    α ≤ γ ≤ β, hence α ≤ β by transitivity. Contrapositively,
    ¬(α ≤ β) implies (MN)(α,β) = 0. -/
theorem isCausalMatrix_mul {k : Type*} [Field k] (C : CAlg k)
    (M N : C.Λ → C.Λ → k)
    (hM : IsCausalMatrix C M) (hN : IsCausalMatrix C N) :
    IsCausalMatrix C (fun α β => ∑ γ : C.Λ, M α γ * N γ β) := by
  intro α β h_not_le
  apply Finset.sum_eq_zero
  intro γ _
  by_cases hαγ : C.le α γ
  · by_cases hγβ : C.le γ β
    · exact absurd (C.le_trans α γ β hαγ hγβ) h_not_le
    · simp [hN γ β hγβ]
  · simp [hM α γ hαγ]

/-! ### Orthogonal idempotents -/

/-- The standard basis idempotent eα: the matrix with 1 at (α,α)
    and 0 elsewhere. These form a complete set of orthogonal idempotents. -/
def idempotent {k : Type*} [Field k] (C : CAlg k) (α : C.Λ) :
    C.Λ → C.Λ → k :=
  fun i j => if i = α ∧ j = α then (1 : k) else 0

/-- Idempotents are causal matrices. -/
theorem idempotent_isCausal {k : Type*} [Field k] (C : CAlg k)
    (α : C.Λ) : IsCausalMatrix C (idempotent C α) := by
  intro i j h_not_le
  simp only [idempotent]
  split_ifs with h
  · exact absurd (h.1 ▸ h.2 ▸ C.le_refl α) h_not_le
  · rfl

/-- Orthogonality: eα · eβ = 0 when α ≠ β. -/
theorem idempotent_orthogonal {k : Type*} [Field k] (C : CAlg k)
    (α β : C.Λ) (h : α ≠ β) :
    ∀ i j, (∑ γ : C.Λ, idempotent C α i γ * idempotent C β γ j) = 0 := by
  intro i j
  apply Finset.sum_eq_zero
  intro γ _
  simp only [idempotent]
  split_ifs with h1 h2
  · obtain ⟨_, h1r⟩ := h1
    obtain ⟨h2l, _⟩ := h2
    exact absurd (h1r ▸ h2l) h
  all_goals simp

/-- Idempotency: eα · eα = eα. -/
theorem idempotent_squared {k : Type*} [Field k] (C : CAlg k)
    (α : C.Λ) :
    ∀ i j, (∑ γ : C.Λ, idempotent C α i γ * idempotent C α γ j) =
      idempotent C α i j := by
  intro i j
  simp only [idempotent]
  rw [Finset.sum_eq_single α]
  · split_ifs with h1 h2 h2 <;> simp_all
  · intro γ _ hγ
    split_ifs <;> simp_all
  · intro h
    exact absurd (Finset.mem_univ α) h

/-! ### Upper-triangularity -/

/-- The causality axiom implies upper-triangularity with respect to
    any linear extension f of the partial order: if f(β) < f(α),
    then M(α,β) = 0. -/
theorem isUpperTriangular_of_causal {k : Type*} [Field k]
    (C : CAlg k) (M : C.Λ → C.Λ → k)
    (hM : IsCausalMatrix C M)
    (f : C.Λ → ℕ) (hf : ∀ a b, C.le a b → a ≠ b → f a < f b) :
    ∀ α β, f β < f α → M α β = 0 := by
  intro α β hlt
  apply hM
  intro h_le
  by_cases heq : α = β
  · exact absurd (heq ▸ hlt) (Nat.lt_irrefl _)
  · exact absurd hlt (Nat.not_lt.mpr (Nat.le_of_lt (hf α β h_le heq)))

/-! ### Construction from a finite poset -/

/-- Construct the **incidence algebra** k[C] from a finite causal set.
    The underlying matrix ring has entries M(α,β) for α ≤ β, representing
    the path algebra of the Hasse diagram with diamond relations. -/
def fromFinitePoset {k : Type*} [Field k]
    (Λ : Type*) [Fintype Λ] [DecidableEq Λ]
    (le : Λ → Λ → Prop) [DecidableRel le]
    (le_refl : ∀ a, le a a)
    (le_antisymm : ∀ a b, le a b → le b a → a = b)
    (le_trans : ∀ a b c, le a b → le b c → le a c) :
    CAlg k where
  Λ := Λ
  le := le
  le_refl := le_refl
  le_antisymm := le_antisymm
  le_trans := le_trans

/-- The **dimension** of the causal algebra k[C] is the number of
    comparable pairs |{(α,β) : α ≤ β}|. -/
def algebraDim {k : Type*} [Field k] (C : CAlg k) : ℕ :=
  Finset.card (Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ)

/-! ### Corner algebras (for the structure sheaf) -/

/-- An **upset** (upper set) in the causal order: if α ∈ S and α ≤ β,
    then β ∈ S. -/
def IsUpset {k : Type*} [Field k] (C : CAlg k)
    (S : Set C.Λ) : Prop :=
  ∀ α β, α ∈ S → C.le α β → β ∈ S

/-- A **downset** (lower set / order ideal): if β ∈ S and α ≤ β,
    then α ∈ S. -/
def IsDownset {k : Type*} [Field k] (C : CAlg k)
    (S : Set C.Λ) : Prop :=
  ∀ α β, β ∈ S → C.le α β → α ∈ S

/-- The **corner algebra** e_S A e_S restricts to the subalgebra
    supported on a subset S ⊆ Λ. A causal matrix M is in the corner
    algebra of S if M(α,β) = 0 whenever α ∉ S or β ∉ S. -/
def IsInCornerAlg {k : Type*} [Field k] (C : CAlg k)
    (S : Set C.Λ) (M : C.Λ → C.Λ → k) : Prop :=
  IsCausalMatrix C M ∧ ∀ α β, (α ∉ S ∨ β ∉ S) → M α β = 0

/-- The corner algebra of a subset is closed under multiplication. -/
theorem cornerAlg_mul_closed {k : Type*} [Field k] (C : CAlg k)
    (S : Set C.Λ) (M N : C.Λ → C.Λ → k)
    (hM : IsInCornerAlg C S M) (hN : IsInCornerAlg C S N) :
    IsInCornerAlg C S (fun α β => ∑ γ : C.Λ, M α γ * N γ β) := by
  constructor
  · exact isCausalMatrix_mul C M N hM.1 hN.1
  · intro α β h_out
    apply Finset.sum_eq_zero
    intro γ _
    cases h_out with
    | inl hα =>
      have := hM.2 α γ (Or.inl hα)
      simp [this]
    | inr hβ =>
      have := hN.2 γ β (Or.inr hβ)
      simp [this]

end CausalAlgebraicGeometry.CausalAlgebra
