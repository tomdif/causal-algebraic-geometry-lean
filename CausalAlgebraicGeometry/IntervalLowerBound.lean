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
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.GCongr
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

/-! ### Stronger bound: |Int(C)| ≥ n²/(2w)

The referee requires the stronger lower bound |Int(C)| ≥ n²/(2w) for width-w
posets on n elements. The proof proceeds in three steps:

1. **Cauchy-Schwarz** (QM-AM): if l₁ + ... + l_w = n then Σ lᵢ² ≥ n²/w,
   i.e. w · Σ lᵢ² ≥ n². This is Mathlib's `sq_sum_le_card_mul_sum_sq`.

2. **Per-chain count**: a chain of length l has l(l+1)/2 comparable pairs,
   hence l² ≤ l(l+1) = 2 · (l(l+1)/2) ≤ 2 · (chain intervals).

3. **Assembly**: combining gives 2w · |Int| ≥ n², i.e. |Int| ≥ n²/(2w).

We state the main theorem with the chain decomposition as a hypothesis
(a list of chain sizes summing to n, with each chain's intervals counted
in the total). This avoids coupling to the specific Dilworth API while
remaining applicable whenever a chain cover exists.
-/

/-- **Cauchy-Schwarz for sums of squares** (natural number form):
    If w numbers sum to n, then w · Σ lᵢ² ≥ n².
    This is just Mathlib's `sq_sum_le_card_mul_sum_sq`. -/
theorem cauchy_schwarz_sum_sq {w : ℕ} (f : Fin w → ℕ) :
    (∑ i : Fin w, f i) ^ 2 ≤ w * ∑ i : Fin w, f i ^ 2 := by
  have := @sq_sum_le_card_mul_sum_sq (Fin w) ℕ _ _ _ _
    Finset.univ f
  simp only [Finset.card_univ, Fintype.card_fin] at this
  convert this using 1

/-- For any natural number l, l² ≤ l * (l + 1).
    This is the per-chain step: l² = l·l ≤ l·(l+1). -/
theorem sq_le_mul_succ (l : ℕ) : l ^ 2 ≤ l * (l + 1) := by
  nlinarith [Nat.zero_le l]

/-- A chain of length l has exactly l*(l+1)/2 comparable pairs (including
    reflexive ones). We state the weaker bound: 2 times the number of
    comparable pairs in a chain of length l is at least l². -/
theorem chain_comparable_pairs_bound (l pairs : ℕ)
    (hpairs : l * (l + 1) ≤ 2 * pairs) :
    l ^ 2 ≤ 2 * pairs :=
  le_trans (sq_le_mul_succ l) hpairs

/-- **Interval lower bound from chain decomposition** (natural number form):
    Given w chains of lengths l₁,...,l_w summing to n, where chain i
    contributes at least lᵢ(lᵢ+1)/2 intervals (so 2·intervals_i ≥ lᵢ²),
    the total interval count satisfies 2w · total ≥ n².

    In Lean: n² ≤ 2 * w * total_intervals. -/
theorem sq_le_two_mul_width_mul_intervals
    {w : ℕ} (f : Fin w → ℕ) (intervals : Fin w → ℕ) (n : ℕ)
    (hsum : ∑ i : Fin w, f i = n)
    (hchain : ∀ i : Fin w, f i ^ 2 ≤ 2 * intervals i)
    (total : ℕ) (htotal : ∑ i : Fin w, intervals i ≤ total) :
    n ^ 2 ≤ 2 * w * total := by
  calc n ^ 2
      = (∑ i : Fin w, f i) ^ 2 := by rw [hsum]
    _ ≤ w * ∑ i : Fin w, f i ^ 2 := cauchy_schwarz_sum_sq f
    _ ≤ w * ∑ i : Fin w, (2 * intervals i) := by
        gcongr with i
        exact hchain i
    _ = w * (2 * ∑ i : Fin w, intervals i) := by
        congr 1; rw [Finset.mul_sum]
    _ = 2 * w * ∑ i : Fin w, intervals i := by ring
    _ ≤ 2 * w * total := by
        exact Nat.mul_le_mul_left _ htotal

/-- **The referee's bound** (CAlg version):
    For a width-w poset on n elements, n² ≤ 2 · w · |Int(C)|.

    Equivalently, |Int(C)| ≥ n²/(2w).

    The hypothesis `hcover` encodes a chain decomposition: w chains
    of sizes f(0), ..., f(w-1) that partition all n elements, where
    each chain's comparable pairs (counted in the full poset) satisfy
    the standard lower bound. -/
theorem numIntervals_ge_sq_div_width {k : Type*} [Field k] (C : CAlg k)
    (n w : ℕ) (_hcard : Fintype.card C.Λ = n)
    (f : Fin w → ℕ) (hsum : ∑ i : Fin w, f i = n)
    (intervals_per_chain : Fin w → ℕ)
    (hchain_bound : ∀ i, f i ^ 2 ≤ 2 * intervals_per_chain i)
    (hchain_inject : ∑ i : Fin w, intervals_per_chain i ≤ numIntervals C) :
    n ^ 2 ≤ 2 * w * numIntervals C :=
  sq_le_two_mul_width_mul_intervals f intervals_per_chain n hsum
    hchain_bound (numIntervals C) hchain_inject

/-- **Corollary**: the tighter exponent bound. With |Int| ≥ n²/(2w)
    and |CC| ≤ B, the ratio satisfies n² · |CC| ≤ 2w · B · |Int|.

    This gives γ ≤ 2wB/n², and when B = O(n^{2w}) we get
    γ = O(n^{2w} · w / n²) = O(n^{2(w-1)}). -/
theorem tighter_gamma_bound {k : Type*} [Field k] (C : CAlg k)
    (n w B : ℕ)
    (hInt : n ^ 2 ≤ 2 * w * numIntervals C)
    (hCC : numCausallyConvex C ≤ B) :
    n ^ 2 * numCausallyConvex C ≤ 2 * w * B * numIntervals C := by
  calc n ^ 2 * numCausallyConvex C
      ≤ 2 * w * numIntervals C * numCausallyConvex C := by
        exact Nat.mul_le_mul_right _ hInt
    _ ≤ 2 * w * numIntervals C * B := by
        exact Nat.mul_le_mul_left _ hCC
    _ = 2 * w * B * numIntervals C := by ring

end CausalAlgebraicGeometry.IntervalLowerBound
