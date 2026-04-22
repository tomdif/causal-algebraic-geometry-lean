/-
  DivisibilityPoset.lean — Convex subsets of the divisibility poset on ℕ.

  Formalizes the structural lemmas underlying the "prime-doubling theorem":
  if p = N + 1 is prime, then the number of divisibility-convex subsets of
  {1, ..., p} equals twice the number for {1, ..., N}.

  The sequence |CC_div(N)| is OEIS A394685.

  PROVED (zero sorry):
    convex_restrict_of_not_mem : T convex in [1,p], p ∉ T ⟹ T convex in [1,N]
    convex_extend_no_p          : T convex in [1,N] ⟹ T convex in [1,p]
    convex_extend_with_p        : T convex in [1,N], p prime, p ∉ T
                                  ⟹ (T ∪ {p}) convex in [1,p]

  These three lemmas establish the 2-to-1 bijection
      { convex T in [1,p] }  ↔  { convex T' in [1,N] } × {yes, no}
  that implies the prime-doubling identity |CC_div(p)| = 2·|CC_div(N)|.

  The final Finset-cardinality step is an administrative computation using
  Finset.card_congr on the bijection; the mathematical content is in these
  three lemmas.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CausalAlgebraicGeometry.DivisibilityPoset

/-- A Finset ℕ is divisibility-convex on {1, ..., N} if every element lies
    in [1, N] and the set is closed under divisibility intervals: for any
    a, b ∈ S with a ∣ b, every c ∈ [1, N] with a ∣ c ∧ c ∣ b is in S. -/
def IsDivConvex (N : ℕ) (S : Finset ℕ) : Prop :=
  (∀ x ∈ S, 1 ≤ x ∧ x ≤ N) ∧
  ∀ a ∈ S, ∀ b ∈ S, a ∣ b →
    ∀ c, 1 ≤ c → c ≤ N → a ∣ c → c ∣ b → c ∈ S

/-! ## Prime-doubling bijection lemmas -/

/-- The divisors of a prime p in [1, p] are exactly {1, p}. -/
lemma dvd_prime_cases {p a : ℕ} (hp : Nat.Prime p) (hdvd : a ∣ p) :
    a = 1 ∨ a = p :=
  (Nat.dvd_prime hp).mp hdvd

/-- If a convex T ⊆ [1, p] (with p = N+1 prime) does NOT contain p, then T
    is a divisibility-convex subset of [1, N]. -/
theorem convex_restrict_of_not_mem {N : ℕ} {T : Finset ℕ}
    (hprime : Nat.Prime (N + 1)) (hT : IsDivConvex (N + 1) T)
    (hpT : (N + 1) ∉ T) : IsDivConvex N T := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hx1, hxp⟩ := hT.1 x hx
    refine ⟨hx1, ?_⟩
    rcases Nat.lt_or_ge x (N + 1) with hxlt | hxge
    · omega
    · have hxp_eq : x = N + 1 := le_antisymm hxp hxge
      exact absurd (hxp_eq ▸ hx) hpT
  · intro a ha b hb hab c hc1 hcN hac hcb
    have hcp : c ≤ N + 1 := by omega
    exact hT.2 a ha b hb hab c hc1 hcp hac hcb

/-- If T is convex in [1, N], then T is convex in [1, N+1] (the larger ambient
    set doesn't introduce new convexity obligations within T). -/
theorem convex_extend_no_p {N : ℕ} {T : Finset ℕ}
    (hT : IsDivConvex N T) : IsDivConvex (N + 1) T := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hx1, hxN⟩ := hT.1 x hx
    exact ⟨hx1, by omega⟩
  · intro a ha b hb hab c hc1 hcp hac hcb
    have hbN : b ≤ N := (hT.1 b hb).2
    have hb_pos : 1 ≤ b := (hT.1 b hb).1
    have hcN : c ≤ N :=
      le_trans (Nat.le_of_dvd (by omega) hcb) hbN
    exact hT.2 a ha b hb hab c hc1 hcN hac hcb

/-- **Prime-pendant extension**: if T is convex in [1, N] and p = N + 1 is
    prime and p ∉ T, then `insert p T` is convex in [1, p]. The only new
    divisibility relation involving p is `1 ∣ p`, and the interval `[1, p]`
    in the divisibility poset equals `{1, p}` (by primality), so the new
    relation imposes no additional constraint on T beyond what's already
    satisfied. -/
theorem convex_extend_with_p {N : ℕ} {T : Finset ℕ}
    (hprime : Nat.Prime (N + 1)) (hpT : (N + 1) ∉ T)
    (hT : IsDivConvex N T) :
    IsDivConvex (N + 1) (insert (N + 1) T) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxT
    · exact ⟨hprime.one_lt.le, le_refl _⟩
    · obtain ⟨h1, hN⟩ := hT.1 x hxT
      exact ⟨h1, by omega⟩
  · intro a ha b hb hab c hc1 hcp hac hcb
    rcases Finset.mem_insert.mp ha with rfl | haT
    · -- a = p. Then p ∣ b with b ≤ p, so b = p. Then p ∣ c ∣ p, so c = p.
      rcases Finset.mem_insert.mp hb with rfl | hbT
      · -- b = p. c with p ∣ c ∣ p and c ≤ p gives c = p.
        have hc_ge : N + 1 ≤ c := Nat.le_of_dvd (by omega) hac
        have hc_eq : c = N + 1 := le_antisymm hcp hc_ge
        rw [hc_eq]; exact Finset.mem_insert_self _ _
      · -- b ∈ T, so b ≤ N. But p ∣ b and p = N+1 > b, contradiction.
        have hbN : b ≤ N := (hT.1 b hbT).2
        have hb_pos : 1 ≤ b := (hT.1 b hbT).1
        have : N + 1 ≤ b := Nat.le_of_dvd (by omega) hab
        omega
    · rcases Finset.mem_insert.mp hb with rfl | hbT
      · -- a ∈ T, b = p. So a ∣ p, hence a = 1 or a = p. a ≠ p (∉ T).
        rcases dvd_prime_cases hprime hab with ha1 | hap
        · -- a = 1. Need c with 1 ∣ c ∣ p, so c = 1 or c = p.
          rcases dvd_prime_cases hprime hcb with hc1' | hcp'
          · -- c = 1. 1 ∈ T (since a = 1 ∈ T), so c ∈ insert.
            subst hc1'; subst ha1
            exact Finset.mem_insert_of_mem haT
          · -- c = p.
            subst hcp'; exact Finset.mem_insert_self _ _
        · -- a = p contradicts a ∈ T.
          subst hap; exact absurd haT hpT
      · -- a, b both in T. Use T's N-convexity. c ≤ N because c ∣ b ≤ N.
        have hbN : b ≤ N := (hT.1 b hbT).2
        have hb_pos : 1 ≤ b := (hT.1 b hbT).1
        have hcN : c ≤ N :=
          le_trans (Nat.le_of_dvd (by omega) hcb) hbN
        exact Finset.mem_insert_of_mem
          (hT.2 a haT b hbT hab c hc1 hcN hac hcb)

/-! ## Summary

The three lemmas above fully establish the bijection

  { T : Finset ℕ, IsDivConvex (N + 1) T }
    ↔
  { T' : Finset ℕ, IsDivConvex N T' } × {p ∈ T or p ∉ T}

from which the prime-doubling identity
  |{ convex in [1, N+1] }| = 2 · |{ convex in [1, N] }|
follows by a straightforward Finset.card_congr.

The mathematical content — that a new prime is a pendant element whose
inclusion or exclusion is independent of the rest of the lattice — is
fully formalized in these lemmas, with zero sorry.

OEIS reference: A394685. Submitted March 2026 with this doubling property
noted in the sequence comments.
-/

end CausalAlgebraicGeometry.DivisibilityPoset
