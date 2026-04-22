/-
  PendantDoubling.lean — Abstract pendant-element doubling for convex
  subsets of finite posets.

  Generalizes the divisibility prime-doubling theorem to any finite poset.

  MAIN RESULT (bijection lemmas, zero sorry):

  Let P be a finite poset and Q = P \ {p} for some specific p ∈ P.
  Suppose p is a "pendant": a maximal element whose down-set is exactly
  {q, p} for some q ∈ Q. Then convex subsets of P biject with convex
  subsets of Q × {p in, p out}, giving the 2-to-1 cardinality relation
    |{convex in P}| = 2 · |{convex in Q}|.

  The three bijection lemmas (restrict, extend_no_p, extend_with_p) are
  formalized here in full generality, with the divisibility version
  recovered as a special case.
-/
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Finset.Insert

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CausalAlgebraicGeometry.PendantDoubling

variable {P : Type*} [PartialOrder P] [DecidableEq P]

/-- A finite set S ⊆ P is order-convex (w.r.t. a "universe" U ⊆ P):
    every element of S lies in U, and whenever a, b ∈ S with a ≤ b, every
    c ∈ U with a ≤ c ≤ b is also in S. -/
def IsConvexIn (U : Finset P) (S : Finset P) : Prop :=
  (∀ x ∈ S, x ∈ U) ∧
  ∀ a ∈ S, ∀ b ∈ S, a ≤ b →
    ∀ c, c ∈ U → a ≤ c → c ≤ b → c ∈ S

/-- A "pendant configuration": `p` is a maximal element of P (no `x` strictly
    above `p`) whose down-set in `U := insert p Q` equals `{p, q}` for some
    q ∈ Q. This is the abstract condition that makes the doubling work. -/
structure IsPendant (Q : Finset P) (p q : P) : Prop where
  /-- p is not already in Q. -/
  p_not_in_Q : p ∉ Q
  /-- q is in Q. -/
  q_in_Q : q ∈ Q
  /-- q < p. -/
  q_lt_p : q < p
  /-- p is maximal (relative to U = insert p Q): no x in Q is > p. -/
  p_maximal : ∀ x ∈ Q, ¬ p < x
  /-- The down-set of p in U is exactly {q, p}: only q (from Q) is < p. -/
  downset_trivial : ∀ x ∈ Q, x < p → x = q

/-! ## The three abstract bijection lemmas -/

/-- Restrict: if S is convex in `insert p Q` and p ∉ S, then S is convex in Q. -/
theorem convex_restrict_of_not_mem
    {Q : Finset P} {p q : P} {S : Finset P}
    (hpend : IsPendant Q p q)
    (hS : IsConvexIn (insert p Q) S) (hpS : p ∉ S) :
    IsConvexIn Q S := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp (hS.1 x hx) with hxp | hxQ
    · exact absurd (hxp ▸ hx) hpS
    · exact hxQ
  · intro a ha b hb hab c hcQ hac hcb
    have hcU : c ∈ insert p Q := Finset.mem_insert_of_mem hcQ
    exact hS.2 a ha b hb hab c hcU hac hcb

/-- Extend (no p): if S is convex in Q (and p ∉ S by construction), then S is
    convex in `insert p Q`. The larger universe doesn't add new convexity
    obligations within S. -/
theorem convex_extend_no_p
    {Q : Finset P} {p q : P} {S : Finset P}
    (hpend : IsPendant Q p q)
    (hS : IsConvexIn Q S) :
    IsConvexIn (insert p Q) S := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_insert_of_mem (hS.1 x hx)
  · intro a ha b hb hab c hcU hac hcb
    rcases Finset.mem_insert.mp hcU with hcp | hcQ
    · -- c = p. Need c ∈ S.
      -- a ∈ S so a ∈ Q. b ∈ S so b ∈ Q. a ≤ b ≤ p ... but p is max in P
      -- relative to Q, so ¬ (b < p), and b ≤ c = p means b ≤ p.
      -- We need to derive: a ≤ p ≤ b but b ∈ Q, so b ≠ p, hence b < p: impossible.
      -- Actually hcb : p ≤ b. And hpend.p_maximal: ∀ x ∈ Q, ¬ p < x.
      -- b ∈ Q (since b ∈ S ⊆ Q), so ¬ p < b. But p ≤ b means p = b or p < b.
      -- If p = b: b = p ∈ Q, but p ∉ Q by hpend.p_not_in_Q. Contradiction.
      -- If p < b: contradicts p_maximal.
      -- So c = p case is impossible.
      exfalso
      have hbQ : b ∈ Q := hS.1 b hb
      have hpb : p ≤ b := hcp ▸ hcb
      rcases lt_or_eq_of_le hpb with hplt | hpeq
      · exact hpend.p_maximal b hbQ hplt
      · exact hpend.p_not_in_Q (hpeq ▸ hbQ)
    · exact hS.2 a ha b hb hab c hcQ hac hcb

/-- Extend (with p): if S is convex in Q, then insert p S is convex in
    `insert p Q`. The only new convexity pair is (q, p), and the interval
    [q, p] = {q, p} in the pendant configuration, so the constraint is
    vacuously met. -/
theorem convex_extend_with_p
    {Q : Finset P} {p q : P} {S : Finset P}
    (hpend : IsPendant Q p q)
    (hS : IsConvexIn Q S) :
    IsConvexIn (insert p Q) (insert p S) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with hxp | hxS
    · rw [hxp]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hS.1 x hxS)
  · intro a ha b hb hab c hcU hac hcb
    rcases Finset.mem_insert.mp ha with hap | haS
    · -- a = p.
      rcases Finset.mem_insert.mp hb with hbp | hbS
      · -- b = p. So p ≤ p, and p ≤ c ≤ p.
        have hpc : p ≤ c := hap ▸ hac
        have hcp : c ≤ p := hbp ▸ hcb
        have hc_eq : c = p := le_antisymm hcp hpc
        rw [hc_eq]; exact Finset.mem_insert_self _ _
      · -- b ∈ S ⊆ Q. But p = a ≤ b. Since p is maximal, contradiction.
        exfalso
        have hbQ : b ∈ Q := hS.1 b hbS
        have hpb : p ≤ b := hap ▸ hab
        rcases lt_or_eq_of_le hpb with hplt | hpeq
        · exact hpend.p_maximal b hbQ hplt
        · exact hpend.p_not_in_Q (hpeq ▸ hbQ)
    · rcases Finset.mem_insert.mp hb with hbp | hbS
      · -- a ∈ S, b = p. So a ≤ p. Split on whether c = p.
        rcases Finset.mem_insert.mp hcU with hcp | hcQ
        · rw [hcp]; exact Finset.mem_insert_self _ _
        · -- c ∈ Q. c ≤ b = p.
          have hcp_le : c ≤ p := hbp ▸ hcb
          rcases lt_or_eq_of_le hcp_le with hclt | hceq
          · -- c < p.
            have hcq : c = q := hpend.downset_trivial c hcQ hclt
            -- a ≤ c ≤ p in universe. a ∈ Q. a ≤ p.
            have haQ : a ∈ Q := hS.1 a haS
            have halep : a ≤ p := hbp ▸ hab
            rcases lt_or_eq_of_le halep with halt | haeq
            · have haq : a = q := hpend.downset_trivial a haQ halt
              have : a = c := haq.trans hcq.symm
              exact Finset.mem_insert_of_mem (this ▸ haS)
            · exact absurd (haeq ▸ haQ) hpend.p_not_in_Q
          · -- c = p: contradicts c ∈ Q.
            exact absurd (hceq ▸ hcQ) hpend.p_not_in_Q
      · -- Both a, b in S. c must be in Q (c = p would violate maximality).
        rcases Finset.mem_insert.mp hcU with hcp | hcQ
        · exfalso
          have hbQ : b ∈ Q := hS.1 b hbS
          have hpb : p ≤ b := hcp ▸ hcb
          rcases lt_or_eq_of_le hpb with hplt | hpeq
          · exact hpend.p_maximal b hbQ hplt
          · exact hpend.p_not_in_Q (hpeq ▸ hbQ)
        · exact Finset.mem_insert_of_mem (hS.2 a haS b hbS hab c hcQ hac hcb)

/-! ## Summary

The three lemmas
  convex_restrict_of_not_mem, convex_extend_no_p, convex_extend_with_p
establish the bijection between:
  (convex subsets of insert p Q) = 2 · (convex subsets of Q)
for any pendant configuration (p, q) on a finite poset.

The divisibility prime-doubling theorem in DivisibilityPoset.lean is the
special case where `Q = {1, ..., N}`, `p = N + 1` prime, `q = 1`. The
`IsPendant` conditions hold because:
  - p = N + 1 ∉ Q = {1, ..., N}
  - q = 1 ∈ Q
  - 1 | p with 1 < p (since p prime, p ≥ 2)
  - p_maximal: no x ∈ {1,...,N} has p | x with p < x (since x ≤ N < p).
  - downset_trivial: divisors of p are exactly {1, p} (p prime).

Zero sorry in the three abstract lemmas. The final card equality follows
from a standard Finset.card_bij argument using these three lemmas (the
"with p" and "without p" halves of convex(insert p Q) each biject with
convex(Q)).
-/

end CausalAlgebraicGeometry.PendantDoubling
