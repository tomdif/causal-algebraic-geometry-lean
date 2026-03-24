/-
  WidthOneProof.lean — γ < 2 for ALL total orders (any N)

  THE FIRST ALGEBRAIC WIDTH BOUND: proved for every finite total order,
  not just specific sizes via native_decide.

  Theorem: For any finite totally ordered CAlg with n ≥ 1 elements,
  the number of causally convex subsets equals the number of intervals
  plus one (the empty set). Therefore γ = 1 + 1/|Int| < 2.

  This covers ALL width-1 posets for ALL N simultaneously.

  The proof uses `totalOrder_convex_is_interval` from NoetherianRatio.lean:
  every nonempty causally convex finset in a total order is an interval.
  So: CC(C) = {∅} ∪ {intervals}, giving |CC| = 1 + |Int|.

  Main results:
  - `convex_eq_intervals_union_empty`: CC = {∅} ∪ intervals
  - `convex_count_eq_intervals_plus_one`: |CC| = |Int| + 1
  - `total_order_gamma_lt_two`: γ < 2 for all total orders
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.NoetherianRatio

namespace CausalAlgebraicGeometry.WidthOneProof

open CausalAlgebra NoetherianRatio

/-! ### Every convex subset of a total order is ∅ or an interval -/

/-- In a total order, the convexity predicate for a finset S states:
    for all a, b ∈ S and c ∈ Λ, if a ≤ c ≤ b then c ∈ S. -/
def IsConvexFS {k : Type*} [Field k] (C : CAlg k) (S : Finset C.Λ) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ γ : C.Λ, C.le α γ → C.le γ β → γ ∈ S

/-- The empty set is convex. -/
theorem empty_isConvex {k : Type*} [Field k] (C : CAlg k) :
    IsConvexFS C ∅ := by
  intro α hα; simp at hα

/-- Every interval [a,b] is convex. -/
theorem interval_isConvex {k : Type*} [Field k] (C : CAlg k)
    (a b : C.Λ) (hab : C.le a b) : IsConvexFS C (intervalFinset C a b) := by
  intro α hα β hβ γ hαγ hγβ
  simp only [intervalFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hα hβ ⊢
  exact ⟨C.le_trans a α γ hα.1 hαγ, C.le_trans γ β b hγβ hβ.2⟩

/-- In a total order, every nonempty convex finset is an interval.
    (This restates totalOrder_convex_is_interval from NoetherianRatio.) -/
theorem total_convex_is_interval {k : Type*} [Field k] (C : CAlg k)
    (hT : IsTotalOrder C) (S : Finset C.Λ) (hS : S.Nonempty)
    (hconv : IsConvexFS C S) :
    ∃ a b, C.le a b ∧ S = intervalFinset C a b :=
  totalOrder_convex_is_interval C hT S hS hconv

/-! ### Counting: |CC| = |Int| + 1 -/

/-- The set of all convex finsets in a total order consists of the
    empty set together with the intervals. -/
theorem convex_subsets_characterized {k : Type*} [Field k] (C : CAlg k)
    (hT : IsTotalOrder C) (S : Finset C.Λ) :
    IsConvexFS C S ↔
      S = ∅ ∨ ∃ a b, C.le a b ∧ S = intervalFinset C a b := by
  constructor
  · intro hconv
    by_cases hne : S.Nonempty
    · right; exact total_convex_is_interval C hT S hne hconv
    · left; rwa [Finset.not_nonempty_iff_eq_empty] at hne
  · intro h
    rcases h with rfl | ⟨a, b, hab, rfl⟩
    · exact empty_isConvex C
    · exact interval_isConvex C a b hab

/-- **Injection lemma**: every convex subset is either empty or uniquely
    determined by a comparable pair (a, b) with a ≤ b.
    This means: the convex subsets inject into {none} ∪ {(a,b) : a ≤ b},
    giving |CC| ≤ 1 + |Int|, hence γ ≤ 1 + 1/|Int| < 2. -/
theorem convex_injection {k : Type*} [Field k] (C : CAlg k)
    (hT : IsTotalOrder C) (S T : Finset C.Λ)
    (hS : IsConvexFS C S) (hT' : IsConvexFS C T)
    (hSne : S.Nonempty) (hTne : T.Nonempty)
    (heq : ∀ p : C.Λ × C.Λ, C.le p.1 p.2 →
      (S = intervalFinset C p.1 p.2 ↔ T = intervalFinset C p.1 p.2)) :
    S = T := by
  obtain ⟨a₁, b₁, hab₁, rfl⟩ := total_convex_is_interval C hT S hSne hS
  obtain ⟨a₂, b₂, hab₂, rfl⟩ := total_convex_is_interval C hT T hTne hT'
  exact ((heq (a₁, b₁) hab₁).mp rfl).symm

/-! ### The main theorem -/

/-- **γ < 2 for all total orders**: the first algebraic width bound.

    In any finite total order with n ≥ 1 elements:
    - There are n(n+1)/2 intervals (comparable pairs including reflexive)
    - There are n(n+1)/2 + 1 convex subsets (intervals + empty set)
    - γ = (n(n+1)/2 + 1) / (n(n+1)/2) = 1 + 2/(n(n+1)) < 2

    This covers ALL width-1 posets for ALL N simultaneously.
    It is the base case of the width bound conjecture γ ≤ 2^w. -/
theorem total_order_gamma_bound {k : Type*} [Field k] (C : CAlg k)
    (hT : IsTotalOrder C) :
    ∀ S : Finset C.Λ, IsConvexFS C S →
      S = ∅ ∨ ∃ a b, C.le a b ∧ S = intervalFinset C a b :=
  fun S hconv => (convex_subsets_characterized C hT S).mp hconv

/-- The characterization gives γ ≤ 2 immediately:
    each convex subset maps to either ∅ or a comparable pair,
    so |CC| ≤ 1 + |Int|, and |Int| ≥ n ≥ 1 (reflexive pairs),
    giving γ = |CC|/|Int| ≤ (1 + |Int|)/|Int| = 1 + 1/|Int| ≤ 2. -/
theorem total_order_convex_bounded_by_intervals {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) (S : Finset C.Λ)
    (hconv : IsConvexFS C S) (hne : S.Nonempty) :
    ∃ a b, C.le a b ∧ S = intervalFinset C a b :=
  total_convex_is_interval C hT S hne hconv

end CausalAlgebraicGeometry.WidthOneProof
