/-
  Separation5.lean -- 5-element separation example

  Two posets on Fin 5 that agree on EIGHT classical order-theoretic
  invariants yet are distinguished by the Noetherian ratio gamma.

  P1 (Diamond + isolated point):
      0 (isolated)    4 -> 1 -> 3
                       4 -> 2 -> 3

  P2 (Y + pendant):
      3 -> 1,  3 -> 2 -> 4,  0 -> 4

  INVARIANT PROFILE:
    Invariant            P1    P2    Same?
    -----------------------------------------------
    Width                 3     3    YES
    Height                3     3    YES
    Hasse edges           4     4    YES
    Antichains           12    12    YES
    Maximal chains        3     3    YES
    Comparable pairs     10    10    YES
    Order ideals         12    12    YES
    Join-irreducibles     2     2    YES
    |CC| (convex)        26    28    NO
    |Int| (intervals)    10    10    YES
    gamma = |CC|/|Int|  26/10 28/10  NO  (gamma separates!)

  This dramatically extends the Separation.lean result: eight invariants
  agree (not just three), yet gamma still separates. The Noetherian ratio
  detects branching geometry invisible to all classical order invariants.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Defs.PartialOrder

namespace CausalAlgebraicGeometry.Separation5

/-! ### P1: Diamond + isolated point

    Element 0 is isolated.
    4 < 1 < 3,  4 < 2 < 3.
    Covers: (4,1), (4,2), (1,3), (2,3).
-/

def p1Le : Fin 5 → Fin 5 → Prop := fun a b =>
  a = b ∨
  (a.val = 4 ∧ b.val = 1) ∨
  (a.val = 4 ∧ b.val = 2) ∨
  (a.val = 4 ∧ b.val = 3) ∨
  (a.val = 1 ∧ b.val = 3) ∨
  (a.val = 2 ∧ b.val = 3)

instance : DecidableRel p1Le := fun a b => by unfold p1Le; exact inferInstance

theorem p1_refl : ∀ a : Fin 5, p1Le a a := fun a => Or.inl rfl

theorem p1_antisymm : ∀ a b : Fin 5, p1Le a b → p1Le b a → a = b := by
  intro a b hab hba; simp only [p1Le] at hab hba; ext; omega

theorem p1_trans : ∀ a b c : Fin 5, p1Le a b → p1Le b c → p1Le a c := by
  intro a b c hab hbc; simp only [p1Le] at hab hbc ⊢; omega

/-! ### P2: Y + pendant

    3 < 1,  3 < 2 < 4,  0 < 4.
    Covers: (3,1), (3,2), (2,4), (0,4).
-/

def p2Le : Fin 5 → Fin 5 → Prop := fun a b =>
  a = b ∨
  (a.val = 3 ∧ b.val = 1) ∨
  (a.val = 3 ∧ b.val = 2) ∨
  (a.val = 3 ∧ b.val = 4) ∨
  (a.val = 2 ∧ b.val = 4) ∨
  (a.val = 0 ∧ b.val = 4)

instance : DecidableRel p2Le := fun a b => by unfold p2Le; exact inferInstance

theorem p2_refl : ∀ a : Fin 5, p2Le a a := fun a => Or.inl rfl

theorem p2_antisymm : ∀ a b : Fin 5, p2Le a b → p2Le b a → a = b := by
  intro a b hab hba; simp only [p2Le] at hab hba; ext; omega

theorem p2_trans : ∀ a b c : Fin 5, p2Le a b → p2Le b c → p2Le a c := by
  intro a b c hab hbc; simp only [p2Le] at hab hbc ⊢; omega

/-! ### Counting functions for Fin 5 -/

/-- Count causally convex subsets. -/
def countConvex5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  (Finset.univ.powerset : Finset (Finset (Fin 5))).filter (fun S =>
    ∀ a ∈ S, ∀ b ∈ S, ∀ c : Fin 5, le a c → le c b → c ∈ S) |>.card

/-- Count comparable pairs (intervals). -/
def countIntervals5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  Finset.univ.filter (fun p : Fin 5 × Fin 5 => le p.1 p.2) |>.card

/-- Count Hasse edges (covers). -/
def countLinks5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  Finset.univ.filter (fun p : Fin 5 × Fin 5 =>
    le p.1 p.2 ∧ p.1 ≠ p.2 ∧
    ∀ c : Fin 5, le p.1 c → le c p.2 → c = p.1 ∨ c = p.2) |>.card

/-- An antichain: no two distinct elements are comparable. -/
def isAntichain5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] (S : Finset (Fin 5)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬le a b

instance (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] (S : Finset (Fin 5)) :
    Decidable (isAntichain5 le S) := by
  unfold isAntichain5; exact inferInstance

/-- Count antichains. -/
def countAntichains5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  (Finset.univ.powerset : Finset (Finset (Fin 5))).filter (fun S =>
    isAntichain5 le S) |>.card

/-- Width: maximum antichain size. -/
def width5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  ((Finset.univ.powerset : Finset (Finset (Fin 5))).filter (fun S =>
    isAntichain5 le S)).sup Finset.card

/-- A chain: every pair is comparable. -/
def isChain5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] (S : Finset (Fin 5)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, le a b ∨ le b a

instance (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] (S : Finset (Fin 5)) :
    Decidable (isChain5 le S) := by
  unfold isChain5; exact inferInstance

/-- Height: maximum chain size. -/
def height5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  ((Finset.univ.powerset : Finset (Finset (Fin 5))).filter (fun S =>
    isChain5 le S)).sup Finset.card

/-- Count maximal chains: chains not properly contained in any other chain. -/
def countMaximalChains5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  let ps := (Finset.univ.powerset : Finset (Finset (Fin 5)))
  let chains := ps.filter (fun S => isChain5 le S)
  chains.filter (fun S => ∀ T ∈ chains, S ⊆ T → T ⊆ S) |>.card

/-- A downset (order ideal): downward-closed. -/
def isDownset5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] (S : Finset (Fin 5)) : Prop :=
  ∀ a : Fin 5, ∀ b ∈ S, le a b → a ∈ S

instance (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] (S : Finset (Fin 5)) :
    Decidable (isDownset5 le S) := by
  unfold isDownset5; exact inferInstance

/-- Count order ideals (downsets). -/
def countDownsets5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  (Finset.univ.powerset : Finset (Finset (Fin 5))).filter (fun S =>
    isDownset5 le S) |>.card

/-- An element is join-irreducible if it has exactly one lower cover. -/
def isJoinIrreducible5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] (x : Fin 5) : Prop :=
  (Finset.univ.filter (fun y : Fin 5 =>
    le y x ∧ y ≠ x ∧
    ∀ c : Fin 5, le y c → le c x → c = y ∨ c = x)).card = 1

instance (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] (x : Fin 5) :
    Decidable (isJoinIrreducible5 le x) := by
  unfold isJoinIrreducible5; exact inferInstance

/-- Count join-irreducible elements. -/
def countJoinIrr5 (le : Fin 5 → Fin 5 → Prop) [DecidableRel le] : ℕ :=
  Finset.univ.filter (fun x : Fin 5 => isJoinIrreducible5 le x) |>.card

/-! ### Computed values for P1 (Diamond + isolated) -/

theorem p1_width : width5 p1Le = 3 := by native_decide
theorem p1_height : height5 p1Le = 3 := by native_decide
theorem p1_links : countLinks5 p1Le = 4 := by native_decide
theorem p1_antichains : countAntichains5 p1Le = 12 := by native_decide
theorem p1_maximalChains : countMaximalChains5 p1Le = 3 := by native_decide
theorem p1_comparable : countIntervals5 p1Le = 10 := by native_decide
theorem p1_downsets : countDownsets5 p1Le = 12 := by native_decide
theorem p1_joinIrr : countJoinIrr5 p1Le = 2 := by native_decide
theorem p1_convex : countConvex5 p1Le = 26 := by native_decide

/-! ### Computed values for P2 (Y + pendant) -/

theorem p2_width : width5 p2Le = 3 := by native_decide
theorem p2_height : height5 p2Le = 3 := by native_decide
theorem p2_links : countLinks5 p2Le = 4 := by native_decide
theorem p2_antichains : countAntichains5 p2Le = 12 := by native_decide
theorem p2_maximalChains : countMaximalChains5 p2Le = 3 := by native_decide
theorem p2_comparable : countIntervals5 p2Le = 10 := by native_decide
theorem p2_downsets : countDownsets5 p2Le = 12 := by native_decide
theorem p2_joinIrr : countJoinIrr5 p2Le = 2 := by native_decide
theorem p2_convex : countConvex5 p2Le = 28 := by native_decide

/-! ### Eight invariants agree -/

theorem same_width : width5 p1Le = width5 p2Le := by
  rw [p1_width, p2_width]

theorem same_height : height5 p1Le = height5 p2Le := by
  rw [p1_height, p2_height]

theorem same_links : countLinks5 p1Le = countLinks5 p2Le := by
  rw [p1_links, p2_links]

theorem same_antichains : countAntichains5 p1Le = countAntichains5 p2Le := by
  rw [p1_antichains, p2_antichains]

theorem same_maximalChains : countMaximalChains5 p1Le = countMaximalChains5 p2Le := by
  rw [p1_maximalChains, p2_maximalChains]

theorem same_comparable : countIntervals5 p1Le = countIntervals5 p2Le := by
  rw [p1_comparable, p2_comparable]

theorem same_downsets : countDownsets5 p1Le = countDownsets5 p2Le := by
  rw [p1_downsets, p2_downsets]

theorem same_joinIrr : countJoinIrr5 p1Le = countJoinIrr5 p2Le := by
  rw [p1_joinIrr, p2_joinIrr]

/-! ### Gamma differs -/

/-- P1 has 26 convex subsets and 10 comparable pairs. -/
theorem p1_gamma_num : countConvex5 p1Le = 26 := p1_convex

/-- P2 has 28 convex subsets and 10 comparable pairs. -/
theorem p2_gamma_num : countConvex5 p2Le = 28 := p2_convex

/-- gamma(P1) = 26/10, gamma(P2) = 28/10. Cross-multiply: 26 * 10 ≠ 28 * 10. -/
theorem gamma_differs :
    countConvex5 p1Le * countIntervals5 p2Le ≠
    countConvex5 p2Le * countIntervals5 p1Le := by native_decide

/-! ### Capstone Theorem -/

/-- **FIVE-ELEMENT SEPARATION THEOREM**: Two 5-element posets agree on
    eight classical order-theoretic invariants (width, height, Hasse edges,
    antichains, maximal chains, comparable pairs, order ideals,
    join-irreducibles) yet are separated by the Noetherian ratio gamma.

    This dramatically strengthens the 4-element result in Separation.lean
    (which matched only 3 invariants). The Noetherian ratio captures
    causal-geometric structure invisible to all eight classical invariants. -/
theorem separation5_theorem :
    -- Eight agreeing invariants
    width5 p1Le = width5 p2Le ∧
    height5 p1Le = height5 p2Le ∧
    countLinks5 p1Le = countLinks5 p2Le ∧
    countAntichains5 p1Le = countAntichains5 p2Le ∧
    countMaximalChains5 p1Le = countMaximalChains5 p2Le ∧
    countIntervals5 p1Le = countIntervals5 p2Le ∧
    countDownsets5 p1Le = countDownsets5 p2Le ∧
    countJoinIrr5 p1Le = countJoinIrr5 p2Le ∧
    -- Gamma differs
    countConvex5 p1Le * countIntervals5 p2Le ≠
    countConvex5 p2Le * countIntervals5 p1Le :=
  ⟨same_width, same_height, same_links, same_antichains,
   same_maximalChains, same_comparable, same_downsets, same_joinIrr,
   gamma_differs⟩

end CausalAlgebraicGeometry.Separation5
