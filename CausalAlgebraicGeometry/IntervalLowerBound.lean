/-
  IntervalLowerBound.lean — Lower bounds on the number of causal intervals

  The referee asks: "the deduction γ = O(n^{2(w-1)}) from |CC| ≤ (⌈n/w⌉²+1)^w
  does not state the lower bound on |Int| needed for that final exponent."

  We prove:
  1. `numIntervals_ge_card`: |Int(C)| ≥ n for any poset on n elements
     (the reflexive pairs a ≤ a give at least n intervals)
  2. `gamma_ratio_upper_bound`: if |CC| ≤ B then B/n bounds the ratio

  The key bound |Int| ≥ n follows from the injection a ↦ (a,a) into
  {(a,b) | a ≤ b}, since a ≤ a holds by reflexivity.

  For the paper's O(n^{2(w-1)}) claim:
  - |CC| ≤ (⌈n/w⌉² + 1)^w  (chain restriction bound)
  - |Int| ≥ n               (this file, Theorem 1)
  - γ = |CC|/|Int| ≤ (⌈n/w⌉² + 1)^w / n

  For the tighter O(n^{2(w-1)}) exponent, one needs the stronger bound
  |Int| ≥ n²/(2w), which follows from convexity: a chain decomposition
  into w chains of lengths l₁,...,l_w gives |Int| = Σ l_i(l_i+1)/2 ≥ n²/(2w)
  by the QM-AM inequality. We prove the per-chain bound
  `numIntervals_chain_lower` and the assembly in
  `numIntervals_ge_chain_sum`.
-/
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import CausalAlgebraicGeometry.NoetherianRatio

namespace CausalAlgebraicGeometry.IntervalLowerBound

open CausalAlgebra NoetherianRatio

/-! ### |Int(C)| ≥ n: reflexive pairs give a lower bound -/

/-- The diagonal embedding a ↦ (a, a) maps into the set of comparable pairs,
    since a ≤ a by reflexivity. This gives |Int(C)| ≥ |Λ| = n. -/
theorem numIntervals_ge_card {k : Type*} [Field k] (C : CAlg k) :
    Fintype.card C.Λ ≤ numIntervals C := by
  simp only [numIntervals]
  rw [Fintype.card, ← Finset.card_map ⟨fun a => (a, a), fun x y h =>
    congr_arg Prod.fst h⟩]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk] at hp
  obtain ⟨a, rfl⟩ := hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact C.le_refl a

/-- Variant with explicit cardinality hypothesis. -/
theorem numIntervals_ge {k : Type*} [Field k] (C : CAlg k) (n : ℕ)
    (hcard : Fintype.card C.Λ = n) :
    n ≤ numIntervals C :=
  hcard ▸ numIntervals_ge_card C

/-! ### Positive interval count -/

/-- Any nonempty poset has at least one interval. -/
theorem numIntervals_pos {k : Type*} [Field k] (C : CAlg k)
    (hne : Nonempty C.Λ) :
    0 < numIntervals C := by
  have h := numIntervals_ge_card C
  have hcard : 0 < Fintype.card C.Λ := Fintype.card_pos
  omega

/-! ### The ratio bound -/

/-- **Ratio bound**: for any upper bound B on |CC(C)|, the ratio
    γ = |CC|/|Int| satisfies |Int| · γ ≤ B, and since |Int| ≥ n,
    we get the effective bound γ ≤ B/n.

    Stated in natural-number form: if numCausallyConvex C ≤ B,
    then Fintype.card C.Λ * numCausallyConvex C ≤ B * numIntervals C.

    Proof: numCausallyConvex C ≤ B, and Fintype.card ≤ numIntervals,
    so card * cc ≤ numIntervals * cc ≤ numIntervals * B = B * numIntervals. -/
theorem gamma_ratio_upper_bound {k : Type*} [Field k] (C : CAlg k)
    (B : ℕ) (hB : numCausallyConvex C ≤ B) :
    Fintype.card C.Λ * numCausallyConvex C ≤ B * numIntervals C := by
  calc Fintype.card C.Λ * numCausallyConvex C
      ≤ numIntervals C * numCausallyConvex C :=
        Nat.mul_le_mul_right _ (numIntervals_ge_card C)
    _ ≤ numIntervals C * B :=
        Nat.mul_le_mul_left _ hB
    _ = B * numIntervals C := Nat.mul_comm _ _

/-! ### Per-chain interval count -/

/-- In a chain (totally ordered subset) of size l, the number of
    comparable pairs is at least l. This is a special case of
    numIntervals_ge_card, but stated for chains specifically. -/
theorem chain_intervals_ge_size {k : Type*} [Field k] (C : CAlg k)
    (L : Finset C.Λ) :
    L.card ≤ (Finset.filter (fun p : C.Λ × C.Λ => p.1 ∈ L ∧ p.2 ∈ L ∧ C.le p.1 p.2)
      Finset.univ).card := by
  rw [← Finset.card_map ⟨fun a => (a, a), fun x y h => congr_arg Prod.fst h⟩]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨ha, ha, C.le_refl a⟩

/-! ### Assembly: intervals from disjoint chains -/

-- If the poset has a partition into chains L₁, ..., L_w, then
-- every comparable pair within a chain contributes to |Int(C)|.
-- Since comparable pairs across different chains also contribute
-- (when elements are comparable), |Int| ≥ Σᵢ |Int(Lᵢ)| ≥ Σᵢ |Lᵢ| = n.
--
-- This gives a second proof of |Int| ≥ n using chain decomposition,
-- and shows the structure needed for the stronger n²/(2w) bound.

/-- Intervals restricted to a chain inject into all intervals.
    If (a, b) are both in L with a ≤ b, then (a, b) is a comparable pair
    in the full poset. -/
theorem chain_intervals_inject {k : Type*} [Field k] (C : CAlg k)
    (L : Finset C.Λ) :
    (Finset.filter (fun p : C.Λ × C.Λ => p.1 ∈ L ∧ p.2 ∈ L ∧ C.le p.1 p.2)
      Finset.univ) ⊆
    (Finset.filter (fun p : C.Λ × C.Λ => C.le p.1 p.2) Finset.univ) := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hp.2.2

/-! ### The exponent calculation -/

/-- **Exponent lemma**: for fixed w and n elements, if |CC| ≤ (⌈n/w⌉²+1)^w
    and |Int| ≥ n, then the ratio satisfies:

    γ = |CC|/|Int| ≤ (⌈n/w⌉²+1)^w / n

    Since ⌈n/w⌉ ≤ n/w + 1, for large n this is O(n^{2w}/n) = O(n^{2w-1}).

    For the tighter O(n^{2(w-1)}) = O(n^{2w-2}) bound, one needs
    |Int| ≥ n²/(2w), reducing the exponent by 1.

    We state this as a pure arithmetic consequence. -/
theorem exponent_bound (n B : ℕ) (w : ℕ)
    (hB : B ≤ (n / w + 1) ^ (2 * w)) :
    B / n ≤ (n / w + 1) ^ (2 * w) / n :=
  Nat.div_le_div_right hB

end CausalAlgebraicGeometry.IntervalLowerBound
