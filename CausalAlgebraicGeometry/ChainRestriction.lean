/-
  ChainRestriction.lean — Convex subsets restrict to intervals on chains

  THE KEY ALGEBRAIC LEMMA for the width bound:

  If S is causally convex in C, L is a chain, and a,b ∈ S ∩ L with
  a ≤ b, then every c ∈ L with a ≤ c ≤ b is also in S.

  This means S ∩ L is "convex within L" — it has no gaps along the
  chain. Combined with injectivity of chain decomposition, this gives
  the counting bound |CC(C)| ≤ ∏(|Int(Lᵢ)| + 1).

  Main results:
  - `convex_fills_chain_gap`: the core lemma (no gaps in S ∩ L)
  - `convex_within_chain`: S ∩ L is convex within L
  - `chain_decomp_injective`: S ↦ (S∩L₁,...,S∩Lw) is injective
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.WidthOneProof

namespace CausalAlgebraicGeometry.ChainRestriction

open CausalAlgebra WidthOneProof

/-! ### Chains as subsets -/

/-- A **chain** in a CAlg: a finset where every pair is comparable. -/
def IsChainFS {k : Type*} [Field k] (C : CAlg k) (L : Finset C.Λ) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, C.le a b ∨ C.le b a

/-! ### The chain restriction lemma -/

/-- **No gaps**: if S is convex in C and a, b ∈ S with a ≤ c ≤ b,
    then c ∈ S. This is just the definition of convexity, but stated
    in the form needed for chain restriction. -/
theorem convex_fills_chain_gap {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (hS : IsConvexFS C S)
    (a b c : C.Λ) (ha : a ∈ S) (hb : b ∈ S)
    (hac : C.le a c) (hcb : C.le c b) :
    c ∈ S :=
  hS a ha b hb c hac hcb

/-- **Convexity within a chain**: if S is convex in C and L is any
    subset, then for a, b ∈ S ∩ L and c ∈ L with a ≤ c ≤ b,
    we have c ∈ S ∩ L.

    This is the chain restriction lemma: S ∩ L has no gaps along L. -/
theorem convex_within_chain {k : Type*} [Field k] (C : CAlg k)
    (S L : Finset C.Λ) (hS : IsConvexFS C S)
    (a b : C.Λ) (ha : a ∈ S ∩ L) (hb : b ∈ S ∩ L)
    (c : C.Λ) (hcL : c ∈ L) (hac : C.le a c) (hcb : C.le c b) :
    c ∈ S ∩ L := by
  rw [Finset.mem_inter] at ha hb ⊢
  exact ⟨hS a ha.1 b hb.1 c hac hcb, hcL⟩

/-- **Symmetry**: the convex-within-chain property works regardless of
    which of a, b is "smaller". If L is a chain, we can always order
    the pair. -/
theorem convex_within_chain_symmetric {k : Type*} [Field k] (C : CAlg k)
    (S L : Finset C.Λ) (hS : IsConvexFS C S) (hL : IsChainFS C L)
    (a b : C.Λ) (ha : a ∈ S ∩ L) (hb : b ∈ S ∩ L)
    (c : C.Λ) (hcL : c ∈ L) :
    (C.le a c ∧ C.le c b) ∨ (C.le b c ∧ C.le c a) → c ∈ S ∩ L := by
  intro h
  cases h with
  | inl h => exact convex_within_chain C S L hS a b ha hb c hcL h.1 h.2
  | inr h => exact convex_within_chain C S L hS b a hb ha c hcL h.1 h.2

/-! ### Injectivity of chain decomposition -/

/-- **Injectivity**: if L₁ ∪ ... ∪ L_w covers all elements, and
    S₁ ∩ Lᵢ = S₂ ∩ Lᵢ for all i, then S₁ = S₂.

    This is the structural core of the counting argument:
    convex subsets inject into tuples of "chain-local" data. -/
theorem chain_decomp_injective {k : Type*} [Field k] (C : CAlg k)
    {w : ℕ} (chains : Fin w → Finset C.Λ)
    (hcover : ∀ x : C.Λ, ∃ i, x ∈ chains i)
    (S₁ S₂ : Finset C.Λ)
    (hrestr : ∀ i, S₁ ∩ chains i = S₂ ∩ chains i) :
    S₁ = S₂ := by
  ext x
  obtain ⟨i, hxi⟩ := hcover x
  have := hrestr i
  constructor
  · intro hx
    have : x ∈ S₁ ∩ chains i := Finset.mem_inter.mpr ⟨hx, hxi⟩
    rw [hrestr i] at this
    exact (Finset.mem_inter.mp this).1
  · intro hx
    have : x ∈ S₂ ∩ chains i := Finset.mem_inter.mpr ⟨hx, hxi⟩
    rw [← hrestr i] at this
    exact (Finset.mem_inter.mp this).1

/-! ### The counting argument (structural) -/

/- **Counting bound (structural form)**: Given a chain decomposition
    into w chains, the number of possible values of S ∩ Lᵢ for a
    convex S is at most |Int(Lᵢ)| + 1 (intervals of Lᵢ plus empty).

    By injectivity, |CC(C)| ≤ ∏ᵢ (|Int(Lᵢ)| + 1).

    For chains of length nᵢ: |Int(Lᵢ)| = nᵢ(nᵢ+1)/2, so the
    bound is ∏ᵢ (nᵢ(nᵢ+1)/2 + 1).

    For a width-w decomposition with chains of equal length N/w:
    |CC| ≤ ((N/w)(N/w+1)/2 + 1)^w ≤ (N²/(2w²) + 1)^w

    When w is fixed and N → ∞: polynomial in N (not exponential).
    When w ~ N (antichain): exponential.

    This is the quantitative Hauptvermutung. -/

/-- **The complete chain restriction package**:
    convexity within chains + injectivity of decomposition. -/
theorem chain_restriction_package {k : Type*} [Field k] (C : CAlg k)
    {w : ℕ} (chains : Fin w → Finset C.Λ)
    (hcover : ∀ x : C.Λ, ∃ i, x ∈ chains i)
    (hchains : ∀ i, IsChainFS C (chains i))
    (S : Finset C.Λ) (hS : IsConvexFS C S) :
    -- S ∩ Lᵢ is convex within Lᵢ for each chain
    (∀ i, ∀ a ∈ S ∩ chains i, ∀ b ∈ S ∩ chains i,
      ∀ c ∈ chains i, C.le a c → C.le c b → c ∈ S ∩ chains i) ∧
    -- The decomposition is injective
    (∀ S₂ : Finset C.Λ,
      (∀ i, S ∩ chains i = S₂ ∩ chains i) → S = S₂) :=
  ⟨fun i a ha b hb c hcL hac hcb =>
    convex_within_chain C S (chains i) hS a b ha hb c hcL hac hcb,
   fun S₂ hrestr => chain_decomp_injective C chains hcover S S₂ hrestr⟩

end CausalAlgebraicGeometry.ChainRestriction
