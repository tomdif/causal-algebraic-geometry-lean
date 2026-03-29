/-
  CausalAlgebraicGeometry/GammaOrdering.lean — Chains minimize gamma

  The Noetherian ratio gamma(C) = |CC(C)| / |Int(C)| measures disorder.
  For chains (total orders), gamma = 1 + 1/|Int| approaches 1.
  For antichains, gamma = 2^n / n grows exponentially.

  Main results:
  - `totalOrder_numCC_eq_numInt_succ`: For total orders, |CC| = |Int| + 1
  - `antichain_numIntervals_eq`: For antichains on n elements, |Int| = n
  - `gamma_chain_lt_gamma_antichain`: gamma(chain) < gamma(antichain) for n >= 2
  - `totalOrder_gamma_excess_eq_one`: The excess |CC| - |Int| = 1 for total orders
    (the ratio gamma = 1 + 1/|Int| converges to 1 as |Int| grows)
-/
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Linarith
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.CausalPrimality
import CausalAlgebraicGeometry.NoetherianRatio

namespace CausalAlgebraicGeometry.GammaOrdering

open CausalAlgebra CausalPrimality NoetherianRatio

/-! ### Total order: |CC| = |Int| + 1 -/

/-- The set of all causally convex finsets. -/
noncomputable def convexFinsets {k : Type*} [Field k] (C : CAlg k) : Finset (Finset C.Λ) :=
  Finset.filter
    (fun S : Finset C.Λ =>
      ∀ α ∈ S, ∀ β ∈ S, ∀ γ : C.Λ, C.le α γ → C.le γ β → γ ∈ S)
    (Finset.univ.powerset)

/-- The set of nonempty causally convex finsets. -/
noncomputable def nonemptyConvexFinsets {k : Type*} [Field k] (C : CAlg k) :
    Finset (Finset C.Λ) :=
  Finset.filter (fun S => S.Nonempty) (convexFinsets C)

/-- The set of comparable pairs (a,b) with a ≤ b. -/
noncomputable def compPairs {k : Type*} [Field k] (C : CAlg k) :
    Finset (C.Λ × C.Λ) :=
  Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ

theorem convexFinsets_card_eq {k : Type*} [Field k] (C : CAlg k) :
    (convexFinsets C).card = numCausallyConvex C := rfl

theorem compPairs_card_eq {k : Type*} [Field k] (C : CAlg k) :
    (compPairs C).card = numIntervals C := rfl

/-- The empty set is the unique convex finset that is not nonempty. -/
theorem convexFinsets_eq_nonempty_insert_empty {k : Type*} [Field k] (C : CAlg k) :
    convexFinsets C = insert ∅ (nonemptyConvexFinsets C) := by
  ext S
  simp only [convexFinsets, nonemptyConvexFinsets, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_powerset]
  constructor
  · intro ⟨hsub, hconv⟩
    by_cases hne : S.Nonempty
    · right; exact ⟨⟨hsub, hconv⟩, hne⟩
    · left; rwa [Finset.not_nonempty_iff_eq_empty] at hne
  · intro h
    cases h with
    | inl h => subst h; exact ⟨Finset.empty_subset _, fun α hα => absurd hα (by simp)⟩
    | inr h => exact h.1

/-- The empty set is not in nonemptyConvexFinsets. -/
theorem empty_not_mem_nonemptyConvex {k : Type*} [Field k] (C : CAlg k) :
    (∅ : Finset C.Λ) ∉ nonemptyConvexFinsets C := by
  simp [nonemptyConvexFinsets, Finset.mem_filter]

/-- |convexFinsets| = |nonemptyConvexFinsets| + 1. -/
theorem convexFinsets_card_succ {k : Type*} [Field k] (C : CAlg k) :
    (convexFinsets C).card = (nonemptyConvexFinsets C).card + 1 := by
  rw [convexFinsets_eq_nonempty_insert_empty]
  rw [Finset.card_insert_of_notMem (empty_not_mem_nonemptyConvex C)]

/-- The interval map sends comparable pairs into convexFinsets. -/
theorem intervalFinset_mem_convex {k : Type*} [Field k] (C : CAlg k)
    (p : C.Λ × C.Λ) (hp : p ∈ compPairs C) :
    intervalFinset C p.1 p.2 ∈ nonemptyConvexFinsets C := by
  simp only [compPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [nonemptyConvexFinsets, convexFinsets, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨⟨Finset.filter_subset _ _, fun α hα β hβ γ hαγ hγβ => ?_⟩, ?_⟩
  · simp only [intervalFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hα hβ ⊢
    exact ⟨C.le_trans p.1 α γ hα.1 hαγ, C.le_trans γ β p.2 hγβ hβ.2⟩
  · exact ⟨p.1, by simp [intervalFinset, Finset.mem_filter]; exact ⟨C.le_refl p.1, hp⟩⟩

/-- The interval map is injective on comparable pairs. -/
theorem intervalFinset_injOn {k : Type*} [Field k] (C : CAlg k) :
    Set.InjOn (fun p : C.Λ × C.Λ => intervalFinset C p.1 p.2) (compPairs C : Set (C.Λ × C.Λ)) := by
  intro p hp q hq heq
  simp only [compPairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  have ⟨h1, h2⟩ := interval_injective C p.1 p.2 q.1 q.2 hp hq heq
  exact Prod.ext h1 h2

/-- For total orders, the interval map is surjective onto nonempty convex finsets. -/
theorem intervalFinset_surj_of_total {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C)
    (S : Finset C.Λ) (hS : S ∈ nonemptyConvexFinsets C) :
    ∃ p ∈ compPairs C, intervalFinset C p.1 p.2 = S := by
  simp only [nonemptyConvexFinsets, convexFinsets, Finset.mem_filter,
    Finset.mem_powerset] at hS
  obtain ⟨⟨_, hconv⟩, hne⟩ := hS
  obtain ⟨a, b, hab, heq⟩ := totalOrder_convex_is_interval C hT S hne hconv
  exact ⟨(a, b), by simp [compPairs, Finset.mem_filter]; exact hab, heq.symm⟩

/-- For total orders, |nonemptyConvexFinsets| = |compPairs|. -/
theorem nonemptyConvex_card_eq_compPairs_of_total {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) :
    (nonemptyConvexFinsets C).card = (compPairs C).card := by
  apply le_antisymm
  · -- Surjectivity: every nonempty convex finset is an interval
    -- So |nonemptyConvex| ≤ |image of compPairs| = |compPairs|
    have hsurj : nonemptyConvexFinsets C ⊆
        Finset.image (fun p : C.Λ × C.Λ => intervalFinset C p.1 p.2) (compPairs C) := by
      intro S hS
      obtain ⟨p, hp, heq⟩ := intervalFinset_surj_of_total C hT S hS
      exact Finset.mem_image.mpr ⟨p, hp, heq⟩
    calc (nonemptyConvexFinsets C).card
        ≤ (Finset.image (fun p => intervalFinset C p.1 p.2) (compPairs C)).card :=
          Finset.card_le_card hsurj
      _ ≤ (compPairs C).card := Finset.card_image_le
  · -- Injectivity: distinct pairs give distinct intervals
    -- So |compPairs| ≤ |nonemptyConvex|
    calc (compPairs C).card
        = (Finset.image (fun p => intervalFinset C p.1 p.2) (compPairs C)).card := by
          rw [Finset.card_image_of_injOn (intervalFinset_injOn C)]
      _ ≤ (nonemptyConvexFinsets C).card := by
          apply Finset.card_le_card
          intro S hS
          obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hS
          exact heq ▸ intervalFinset_mem_convex C p hp

/-- **Key structural theorem**: For total orders, |CC| = |Int| + 1.
    Every nonempty causally convex subset is a unique interval, plus the empty set. -/
theorem totalOrder_numCC_eq_numInt_succ {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) :
    numCausallyConvex C = numIntervals C + 1 := by
  rw [← convexFinsets_card_eq, ← compPairs_card_eq]
  rw [convexFinsets_card_succ]
  rw [nonemptyConvex_card_eq_compPairs_of_total C hT]

/-! ### Antichain: |Int| = n -/

/-- For an antichain on n elements, every comparable pair is reflexive,
    so |Int| = n. -/
theorem antichain_numIntervals_eq {k : Type*} [Field k]
    (C : CAlg k) (n : ℕ)
    (hcard : Fintype.card C.Λ = n)
    (hanti : ∀ α β : C.Λ, α ≠ β → AreIncomparable C α β) :
    numIntervals C = n := by
  simp only [numIntervals]
  -- The comparable pairs are exactly the diagonal: {(a,a) | a ∈ Λ}
  have : Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ =
      Finset.image (fun a => (a, a)) Finset.univ := by
    ext ⟨a, b⟩
    constructor
    · intro hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      by_cases heq : a = b
      · subst heq; exact ⟨a, rfl⟩
      · exact absurd hp (hanti a b heq).1
    · intro hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨c, hc⟩ := hp
      have hab : c = a ∧ c = b := Prod.mk.inj hc
      rw [← hab.1, ← hab.2]; exact C.le_refl c
  rw [this, Finset.card_image_of_injective _ (fun a b h => by
    exact (Prod.mk.inj h).1)]
  rw [Finset.card_univ, hcard]

/-! ### Arithmetic lemmas -/

/-- 2 * n ≤ 2^n for all n ≥ 1. -/
theorem two_mul_le_two_pow (n : ℕ) (hn : 1 ≤ n) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ k =>
      have hk : 1 ≤ k + 1 := by omega
      calc 2 * (k + 2) = 2 * (k + 1) + 2 := by ring
        _ ≤ 2 ^ (k + 1) + 2 := by linarith [ih hk]
        _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := by
            have : 2 ≤ 2 ^ (k + 1) := by
              calc 2 = 2 ^ 1 := by ring
                _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) hk
            linarith
        _ = 2 ^ (k + 2) := by ring

/-- The main arithmetic inequality: for I ≥ 2 and 2n ≤ 2^n,
    we have (I + 1) * n < 2^n * I. -/
theorem cross_mul_ineq (I n : ℕ) (hI : 2 ≤ I) (hn : 2 ≤ n) :
    (I + 1) * n < 2 ^ n * I := by
  -- (I + 1) * n = I * n + n < 2 * I * n = I * (2 * n) ≤ I * 2^n = 2^n * I
  have h1 : I + 1 < 2 * I := by omega
  have h2 : 2 * n ≤ 2 ^ n := two_mul_le_two_pow n (by omega)
  calc (I + 1) * n < 2 * I * n := by nlinarith
    _ = I * (2 * n) := by ring
    _ ≤ I * 2 ^ n := Nat.mul_le_mul_left I h2
    _ = 2 ^ n * I := by ring

/-! ### Total orders have numIntervals ≥ 2 when n ≥ 2 -/

/-- A total order on n ≥ 2 elements has at least 3 comparable pairs
    (and in particular ≥ 2). -/
theorem totalOrder_numInt_ge_two {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C)
    (h_card : 2 ≤ Fintype.card C.Λ) :
    2 ≤ numIntervals C := by
  simp only [numIntervals]
  -- There exist distinct elements a, b
  have ⟨a, b, hab⟩ : ∃ a b : C.Λ, a ≠ b := by
    by_contra h
    push_neg at h
    have : Fintype.card C.Λ ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => h a b⟩
    omega
  -- WLOG a ≤ b (total order)
  obtain hle | hle := hT a b
  · -- (a,a) and (a,b) are both comparable pairs, and they're distinct
    have h1 : (a, a) ∈ Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ := by
      simp [C.le_refl]
    have h2 : (a, b) ∈ Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ := by
      simp [hle]
    have hne : (a, a) ≠ (a, b) := by
      intro h; exact hab (Prod.mk.inj h).2
    calc 2 = ({(a, a), (a, b)} : Finset (C.Λ × C.Λ)).card := by
            rw [Finset.card_pair hne]
      _ ≤ (Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ).card :=
            Finset.card_le_card (fun p hp => by
              simp [Finset.mem_insert, Finset.mem_singleton] at hp
              cases hp with
              | inl h => subst h; exact h1
              | inr h => subst h; exact h2)
  · -- (b,b) and (b,a) are both comparable pairs
    have h1 : (b, b) ∈ Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ := by
      simp [C.le_refl]
    have h2 : (b, a) ∈ Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ := by
      simp [hle]
    have hne : (b, b) ≠ (b, a) := by
      intro h; exact hab (Prod.mk.inj h).2.symm
    calc 2 = ({(b, b), (b, a)} : Finset (C.Λ × C.Λ)).card := by
            rw [Finset.card_pair hne]
      _ ≤ (Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ).card :=
            Finset.card_le_card (fun p hp => by
              simp [Finset.mem_insert, Finset.mem_singleton] at hp
              cases hp with
              | inl h => subst h; exact h1
              | inr h => subst h; exact h2)

/-! ### Main theorem: gamma(chain) < gamma(antichain) -/

/-- **Gamma ordering theorem**: For n ≥ 2, the Noetherian ratio of any
    total order on n elements is strictly less than that of any antichain
    on n elements.

    In cross-multiplied form (avoiding division):
      numCC(chain) * numInt(antichain) < numCC(antichain) * numInt(chain)

    Proof: For total orders, numCC = numInt + 1, so the LHS is (I+1)*n.
    For antichains, numCC = 2^n, numInt = n, so the RHS is 2^n * I.
    The inequality (I+1)*n < 2^n * I follows from I ≥ 2 and 2n ≤ 2^n. -/
theorem gamma_chain_lt_gamma_antichain {k : Type*} [Field k]
    (C_chain C_anti : CAlg k)
    (n : ℕ) (hn : 2 ≤ n)
    -- C_chain is a total order on n elements
    (hchain_card : Fintype.card C_chain.Λ = n)
    (hchain_total : IsTotalOrder C_chain)
    -- C_anti is an antichain on n elements
    (hanti_card : Fintype.card C_anti.Λ = n)
    (hanti : ∀ α β : C_anti.Λ, α ≠ β → AreIncomparable C_anti α β) :
    numCausallyConvex C_chain * numIntervals C_anti <
      numCausallyConvex C_anti * numIntervals C_chain := by
  -- Compute the counts
  rw [totalOrder_numCC_eq_numInt_succ C_chain hchain_total]
  rw [antichain_numIntervals_eq C_anti n hanti_card hanti]
  rw [antichain_numConvex C_anti n hanti_card hanti]
  -- Now the goal is: (numIntervals C_chain + 1) * n < 2^n * numIntervals C_chain
  exact cross_mul_ineq (numIntervals C_chain) n
    (totalOrder_numInt_ge_two C_chain hchain_total (by omega))
    hn

/-! ### Asymptotic: gamma(chain) → 1 -/

/-- For total orders, the gap between |CC| and |Int| is exactly 1.
    Since gamma = |CC|/|Int| = 1 + 1/|Int|, and |Int| grows with n,
    the ratio gamma approaches 1. -/
theorem totalOrder_gamma_excess_eq_one {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) :
    numCausallyConvex C - numIntervals C = 1 := by
  have h := totalOrder_numCC_eq_numInt_succ C hT
  omega

/-- Quantitative convergence: for any bound M, if the total order has
    |Int| ≥ M, then M * (|CC| - |Int|) ≤ |Int|. Equivalently,
    gamma - 1 = 1/|Int| ≤ 1/M. -/
theorem totalOrder_gamma_convergence {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) (M : ℕ) (hM : M ≤ numIntervals C) :
    M * (numCausallyConvex C - numIntervals C) ≤ numIntervals C := by
  rw [totalOrder_gamma_excess_eq_one C hT]
  simp
  exact hM

/-- For any M, a total order on at least M elements has |Int| ≥ M
    (since |Int| ≥ n for any poset on n elements). -/
theorem totalOrder_numInt_ge_card {k : Type*} [Field k] (C : CAlg k) :
    Fintype.card C.Λ ≤ numIntervals C := by
  simp only [numIntervals]
  -- The diagonal map a ↦ (a,a) injects Λ into comparable pairs
  calc Fintype.card C.Λ
      = Finset.card Finset.univ := (Finset.card_univ).symm
    _ = (Finset.image (fun a : C.Λ => (a, a)) Finset.univ).card := by
        rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
    _ ≤ (Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨a, ha⟩ := hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← ha]; exact C.le_refl a

/-- Combining: for any M, a total order on n ≥ M elements has
    gamma - 1 ≤ 1/M (in the natural number sense: M * 1 ≤ |Int|). -/
theorem totalOrder_gamma_vanishes {k : Type*} [Field k]
    (C : CAlg k) (hT : IsTotalOrder C) (M : ℕ) (hM : M ≤ Fintype.card C.Λ) :
    M * (numCausallyConvex C - numIntervals C) ≤ numIntervals C :=
  totalOrder_gamma_convergence C hT M (le_trans hM (totalOrder_numInt_ge_card C))

end CausalAlgebraicGeometry.GammaOrdering
