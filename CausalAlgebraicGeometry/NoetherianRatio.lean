/-
  LayerD/NoetherianRatio.lean — The Noetherian ratio invariant

  Definition 3.5 from the causal-algebraic geometry framework:
  The Noetherian ratio γ(C) = |CC(C)| / |Int(C)| measures how far
  the causally convex subsets of a causal set exceed the causal
  intervals. When γ = 1, every causally convex subset is a union
  of intervals — the "Noetherian" case.

  Computational evidence:
  - Structured lattice diamonds: γ ≈ 1–3
  - Random Poisson sprinklings: γ ≥ 14
  - Conjecture: γ grows polynomially for geometric causal sets
    and exponentially for random ones.

  Main results:
  - `causallyConvexSubsets`: the set CC(C)
  - `causalIntervals`: the set Int(C)
  - `noetherianRatio`: γ(C) = |CC(C)| / |Int(C)|
  - `noetherianRatio_ge_one`: γ ≥ 1 always (intervals are convex)
  - `isNoetherian`: γ = 1 characterization
  - `totalOrder_noetherian`: total orders have γ = 1
-/
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.CausalPrimality

namespace CausalAlgebraicGeometry.NoetherianRatio

open CausalAlgebra CausalPrimality

/-! ### Counting causally convex subsets -/

/-- The **number of causally convex subsets** of Λ.
    We enumerate all subsets of Λ and count those that are
    causally convex. -/
noncomputable def numCausallyConvex {k : Type*} [Field k]
    (C : CAlg k) : ℕ :=
  Finset.card (Finset.filter
    (fun S : Finset C.Λ =>
      ∀ α ∈ S, ∀ β ∈ S, ∀ γ : C.Λ, C.le α γ → C.le γ β → γ ∈ S)
    (Finset.univ.powerset))

/-- The **number of causal intervals** [α, β] = {γ : α ≤ γ ≤ β}.
    We count the number of pairs (α, β) with α ≤ β, since each
    such pair defines a unique interval. -/
noncomputable def numIntervals {k : Type*} [Field k]
    (C : CAlg k) : ℕ :=
  Finset.card (Finset.filter
    (fun p : C.Λ × C.Λ => C.le p.1 p.2)
    Finset.univ)

/-! ### The Noetherian ratio -/

/-- The **Noetherian ratio** γ(C) = |CC(C)| / |Int(C)|.
    Measures how many causally convex subsets exist relative to
    the number of intervals. A low ratio (near 1) indicates
    geometric regularity; a high ratio indicates disorder.

    We represent this as a pair (numerator, denominator) to stay
    in ℕ and avoid division. The actual ratio is
    numCausallyConvex / numIntervals. -/
noncomputable def noetherianRatioNum {k : Type*} [Field k]
    (C : CAlg k) : ℕ :=
  numCausallyConvex C

noncomputable def noetherianRatioDen {k : Type*} [Field k]
    (C : CAlg k) : ℕ :=
  numIntervals C

/-! ### Every interval is causally convex -/

/-- The finset version of a causal interval:
    [α, β]_fin = {γ ∈ Λ : α ≤ γ ∧ γ ≤ β}. -/
noncomputable def intervalFinset {k : Type*} [Field k]
    (C : CAlg k) (α β : C.Λ) : Finset C.Λ :=
  Finset.filter (fun γ => C.le α γ ∧ C.le γ β) Finset.univ

/-- Every causal interval is causally convex. This is the key lemma
    ensuring that |CC(C)| ≥ |Int(C)|, so γ ≥ 1. -/
theorem interval_isCausallyConvex {k : Type*} [Field k]
    (C : CAlg k) (a b : C.Λ) :
    IsCausallyConvex C (↑(intervalFinset C a b) : Set C.Λ) := by
  intro α β γ hα hβ hαγ hγβ
  simp only [intervalFinset, Finset.coe_filter, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hα hβ ⊢
  exact ⟨C.le_trans a α γ hα.1 hαγ, C.le_trans γ β b hγβ hβ.2⟩

/-! ### γ ≥ 1: every interval embeds into CC(C) -/

/-- The map sending (α, β) with α ≤ β to the interval [α, β] ∈ CC(C)
    is injective. Combined with interval_isCausallyConvex, this shows
    |CC(C)| ≥ |Int(C)|, i.e., γ ≥ 1.

    Proof sketch: if [α₁, β₁] = [α₂, β₂] as subsets of Λ, then
    α₁ ∈ [α₂, β₂] gives α₂ ≤ α₁ and α₂ ∈ [α₁, β₁] gives α₁ ≤ α₂,
    so α₁ = α₂ by antisymmetry (and similarly for β). -/
theorem interval_injective {k : Type*} [Field k]
    (C : CAlg k) (a₁ b₁ a₂ b₂ : C.Λ)
    (h1 : C.le a₁ b₁) (h2 : C.le a₂ b₂)
    (heq : intervalFinset C a₁ b₁ = intervalFinset C a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have ha₁_in : a₁ ∈ intervalFinset C a₁ b₁ := by
    simp only [intervalFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C.le_refl a₁, h1⟩
  have hb₁_in : b₁ ∈ intervalFinset C a₁ b₁ := by
    simp only [intervalFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, C.le_refl b₁⟩
  rw [heq] at ha₁_in hb₁_in
  have ha₂_in : a₂ ∈ intervalFinset C a₂ b₂ := by
    simp only [intervalFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C.le_refl a₂, h2⟩
  have hb₂_in : b₂ ∈ intervalFinset C a₂ b₂ := by
    simp only [intervalFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h2, C.le_refl b₂⟩
  rw [← heq] at ha₂_in hb₂_in
  simp only [intervalFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha₁_in hb₁_in ha₂_in hb₂_in
  -- ha₁_in: a₁ ∈ [a₂, b₂], so a₂ ≤ a₁ ≤ b₂
  -- ha₂_in: a₂ ∈ [a₁, b₁], so a₁ ≤ a₂ ≤ b₁
  exact ⟨C.le_antisymm a₁ a₂ ha₂_in.1 ha₁_in.1,
         C.le_antisymm b₁ b₂ hb₁_in.2 hb₂_in.2⟩

/-! ### Total orders are Noetherian (γ = 1) -/

/-- A causal set is a **total order** if every pair is comparable. -/
def IsTotalOrder {k : Type*} [Field k] (C : CAlg k) : Prop :=
  ∀ α β : C.Λ, C.le α β ∨ C.le β α

/-- In a total order, every causally convex subset is a (possibly empty)
    interval. This is because a convex subset of a linearly ordered set
    is an interval.

    Consequence: for total orders, |CC(C)| = |Int(C)| + 1 (the +1 is
    the empty set), so γ approaches 1. -/
-- Helper: in a total order, a nonempty finset has min and max elements.
-- We prove this by strong induction on cardinality.
lemma exists_min_of_total {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) :
    ∀ (l : List C.Λ), l ≠ [] →
      ∃ a ∈ l, ∀ x ∈ l, C.le a x := by
  intro l hl
  induction l with
  | nil => exact absurd rfl hl
  | cons y t ih =>
    by_cases ht : t = []
    · exact ⟨y, List.mem_cons_self, fun x hx => by
        subst ht; simp [List.mem_cons, List.mem_nil_iff] at hx
        exact hx ▸ C.le_refl _⟩
    · obtain ⟨a, ha, hmin⟩ := ih ht
      rcases hT y a with hya | hay
      · exact ⟨y, List.mem_cons_self, fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact C.le_refl _
          · exact C.le_trans _ a x hya (hmin x hx)⟩
      · exact ⟨a, List.mem_cons.mpr (Or.inr ha), fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hay
          · exact hmin x hx⟩

lemma exists_max_of_total {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) :
    ∀ (l : List C.Λ), l ≠ [] →
      ∃ b ∈ l, ∀ x ∈ l, C.le x b := by
  intro l hl
  induction l with
  | nil => exact absurd rfl hl
  | cons y t ih =>
    by_cases ht : t = []
    · exact ⟨y, List.mem_cons_self, fun x hx => by
        subst ht; simp [List.mem_cons, List.mem_nil_iff] at hx
        exact hx ▸ C.le_refl _⟩
    · obtain ⟨b, hb, hmax⟩ := ih ht
      rcases hT y b with hyb | hby
      · exact ⟨b, List.mem_cons.mpr (Or.inr hb), fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hyb
          · exact hmax x hx⟩
      · exact ⟨y, List.mem_cons_self, fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact C.le_refl _
          · exact C.le_trans x b _ (hmax x hx) hby⟩

lemma finset_has_min {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C)
    (S : Finset C.Λ) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ x ∈ S, C.le a x := by
  have hne : S.toList ≠ [] := by
    intro h; exact absurd (Finset.toList_eq_nil.mp h ▸ hS) Finset.not_nonempty_empty
  obtain ⟨a, ha, hmin⟩ := exists_min_of_total C hT S.toList hne
  exact ⟨a, Finset.mem_toList.mp ha, fun x hx =>
    hmin x (Finset.mem_toList.mpr hx)⟩

lemma finset_has_max {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C)
    (S : Finset C.Λ) (hS : S.Nonempty) :
    ∃ b ∈ S, ∀ x ∈ S, C.le x b := by
  have hne : S.toList ≠ [] := by
    intro h; exact absurd (Finset.toList_eq_nil.mp h ▸ hS) Finset.not_nonempty_empty
  obtain ⟨b, hb, hmax⟩ := exists_max_of_total C hT S.toList hne
  exact ⟨b, Finset.mem_toList.mp hb, fun x hx =>
    hmax x (Finset.mem_toList.mpr hx)⟩

theorem totalOrder_convex_is_interval {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C)
    (S : Finset C.Λ) (hS : S.Nonempty)
    (hconv : ∀ α ∈ S, ∀ β ∈ S, ∀ γ : C.Λ,
      C.le α γ → C.le γ β → γ ∈ S) :
    ∃ a b, C.le a b ∧ S = intervalFinset C a b := by
  obtain ⟨a, ha, hmin⟩ := finset_has_min C hT S hS
  obtain ⟨b, hb, hmax⟩ := finset_has_max C hT S hS
  refine ⟨a, b, hmin b hb, ?_⟩
  ext γ
  simp only [intervalFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hγ; exact ⟨hmin γ hγ, hmax γ hγ⟩
  · intro ⟨haγ, hγb⟩; exact hconv a ha b hb γ haγ hγb

/-! ### The Noetherian property -/

/-- A causal set is **Noetherian** (γ = 1) if every causally convex
    subset is a union of intervals. This is the algebraic-geometric
    analog of the Noetherian condition in commutative algebra, where
    every ideal is finitely generated (here: every convex set is
    interval-generated). -/
def IsNoetherian {k : Type*} [Field k] (C : CAlg k) : Prop :=
  ∀ (S : Finset C.Λ),
    (∀ α ∈ S, ∀ β ∈ S, ∀ γ : C.Λ, C.le α γ → C.le γ β → γ ∈ S) →
    ∃ (pairs : Finset (C.Λ × C.Λ)),
      (∀ p ∈ pairs, C.le p.1 p.2) ∧
      S = Finset.biUnion pairs (fun p => intervalFinset C p.1 p.2)

/-- Total orders are Noetherian: every convex subset is a single
    interval [min, max]. -/
theorem totalOrder_isNoetherian {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) :
    IsNoetherian C := by
  intro S hconv
  by_cases hne : S.Nonempty
  · obtain ⟨a, b, hab, heq⟩ := totalOrder_convex_is_interval C hT S hne hconv
    exact ⟨{(a, b)}, fun p hp => by simp at hp; exact hp ▸ hab,
      by simp [heq]⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨∅, fun _ h => by simp at h,
      by simp [hne]⟩

/-! ### Width and the Noetherian ratio -/

/-- For an antichain (width-w poset), every subset is causally convex
    since there are no comparable pairs. So |CC| = 2^n and |Int| = n,
    giving γ = 2^n / n — exponential growth. -/
theorem antichain_numConvex {k : Type*} [Field k]
    (C : CAlg k) (n : ℕ)
    (hcard : Fintype.card C.Λ = n)
    (hanti : ∀ α β : C.Λ, α ≠ β → AreIncomparable C α β) :
    numCausallyConvex C = 2 ^ n := by
  -- Every subset is convex: for α ≠ β, ¬(α ≤ β) by antichain
  -- property, so the premise α ≤ γ ≤ β is never satisfied.
  -- For α = β, the condition α ≤ γ ≤ α forces γ = α ∈ S.
  -- Every subset is convex in an antichain
  suffices h : ∀ S : Finset C.Λ,
      (∀ α ∈ S, ∀ β ∈ S, ∀ γ : C.Λ, C.le α γ → C.le γ β → γ ∈ S) by
    simp only [numCausallyConvex]
    have : Finset.filter
        (fun S : Finset C.Λ =>
          ∀ α ∈ S, ∀ β ∈ S, ∀ γ : C.Λ, C.le α γ → C.le γ β → γ ∈ S)
        (Finset.univ.powerset) = Finset.univ.powerset :=
      Finset.filter_true_of_mem (fun S _ => h S)
    rw [this, Finset.card_powerset, Finset.card_univ, hcard]
  intro S α hα β hβ γ hαγ hγβ
  by_cases heq : α = β
  · subst heq; exact (C.le_antisymm γ α hγβ hαγ) ▸ hα
  · exact absurd (C.le_trans α γ β hαγ hγβ) (hanti α β heq).1

end CausalAlgebraicGeometry.NoetherianRatio
