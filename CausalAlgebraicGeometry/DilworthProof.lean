/-
  DilworthProof.lean — Proving the Dilworth inductive step

  Goal: prove `dilworth_inductive_step`, which provides the hypothesis
  `h_step` needed by `dilworth_from_inductive_step` in Dilworth.lean.

  Statement: for any nonempty finite poset S with inducedWidth(S) > 0,
  there exists a chain L ⊆ S such that inducedWidth(S \ L) < inducedWidth(S).

  Proof strategy (standard induction on |S|, NO Hall's theorem):
  We first prove `dilworth_full_cover`: every S can be covered by
  ≤ inducedWidth(S) chains that are subsets of S. Then h_step follows
  from the pigeonhole lemma (width ≤ number of covering chains).

  The full cover uses strong induction on |S|:
  1. |S| = width(S): S is an antichain, covered by singleton chains.
  2. |S| > width(S), universal element exists: remove it, IH on remainder.
  3. |S| > width(S), no universal element: C+/C- decomposition + merge.
     This case carries a sorry (the chain merge at the antichain A).
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.ChainRestriction
import CausalAlgebraicGeometry.Dilworth

namespace CausalAlgebraicGeometry.DilworthProof

open CausalAlgebra ChainRestriction Dilworth

/-! ### Auxiliary lemmas about antichains and width -/

/-- An antichain in S witnesses a lower bound on inducedWidth(S). -/
theorem antichain_card_le_inducedWidth {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A) :
    A.card ≤ inducedWidth C S := by
  unfold inducedWidth
  apply Finset.le_sup_of_le (Finset.mem_powerset.mpr hAS)
  split_ifs with h
  · exact le_refl _
  · exact absurd hA h

/-- The inducedWidth of any set is at most its cardinality. -/
theorem inducedWidth_le_card {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) :
    inducedWidth C S ≤ S.card := by
  unfold inducedWidth
  apply Finset.sup_le
  intro A hA
  split_ifs
  · exact Finset.card_le_card (Finset.mem_powerset.mp hA)
  · exact Nat.zero_le _

/-- Width of empty set is 0. -/
theorem inducedWidth_empty {k : Type*} [Field k] (C : CAlg k) :
    inducedWidth C (∅ : Finset C.Λ) = 0 := by
  have h := inducedWidth_le_card C (∅ : Finset C.Λ)
  simp at h; omega

/-! ### Width-1 case -/

/-- If inducedWidth = 1, then all elements of S are pairwise comparable. -/
theorem width_one_total {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (hw : inducedWidth C S = 1) :
    ∀ a ∈ S, ∀ b ∈ S, C.le a b ∨ C.le b a := by
  intro a ha b hb
  by_contra h
  push_neg at h
  have hne : a ≠ b := fun heq => by subst heq; exact h.1 (C.le_refl a)
  have hAC : IsAntichain C {a, b} := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact ⟨h.1, h.2⟩
    · exact ⟨h.2, h.1⟩
    · exact absurd rfl hxy
  have : 2 ≤ inducedWidth C S := by
    calc 2 = ({a, b} : Finset C.Λ).card := (Finset.card_pair hne).symm
      _ ≤ inducedWidth C S :=
          antichain_card_le_inducedWidth C S _ (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption) hAC
  omega

/-! ### Every element is comparable to some max antichain element -/

/-- If A is a maximum antichain in S and x ∈ S \ A, then x is comparable
    to some element of A. -/
theorem comparable_to_max_antichain {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hmax : A.card = inducedWidth C S)
    (x : C.Λ) (hxS : x ∈ S) (hxA : x ∉ A) :
    ∃ a ∈ A, C.le a x ∨ C.le x a := by
  by_contra h
  push_neg at h
  have hAx : IsAntichain C (insert x A) := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact ⟨(h b hb).2, (h b hb).1⟩
    · exact h a ha
    · exact hA a ha b hb hab
  have hle : (insert x A).card ≤ inducedWidth C S :=
    antichain_card_le_inducedWidth C S _
      (by intro y hy; rw [Finset.mem_insert] at hy; rcases hy with rfl | hy; exact hxS; exact hAS hy) hAx
  have := Finset.card_insert_of_notMem hxA
  omega

/-! ### Existence of a max antichain witnessing width -/

/-- There exists an antichain in S achieving the maximum width. -/
theorem exists_max_antichain {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (hw : inducedWidth C S > 0) :
    ∃ A : Finset C.Λ, A ⊆ S ∧ IsAntichain C A ∧ A.card = inducedWidth C S := by
  have hne_pow : S.powerset.Nonempty := ⟨∅, Finset.empty_mem_powerset S⟩
  set f : Finset C.Λ → ℕ := fun A =>
    if ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ C.le a b ∧ ¬ C.le b a then A.card else 0
  have hdef : inducedWidth C S = Finset.sup S.powerset f := rfl
  obtain ⟨A, hA_mem, hA_val⟩ := Finset.exists_mem_eq_sup S.powerset hne_pow f
  have hAS : A ⊆ S := Finset.mem_powerset.mp hA_mem
  rw [hdef] at hw; rw [hA_val] at hw
  simp only [f] at hw ⊢
  split_ifs at hw with hAC
  · exact ⟨A, hAS, hAC, by rw [hdef, hA_val]; simp only [f, if_pos hAC]⟩
  · omega

/-! ### Key lemma: removing an element in every max antichain -/

/-- If every antichain of size w in S contains m, then width(S \ {m}) < w. -/
theorem width_decreases_when_in_every_antichain {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (m : C.Λ) (hw : inducedWidth C S > 0)
    (h_in_every : ∀ B : Finset C.Λ, B ⊆ S → IsAntichain C B →
      B.card = inducedWidth C S → m ∈ B) :
    inducedWidth C (S \ {m}) < inducedWidth C S := by
  by_contra hle
  push_neg at hle
  have hmono : inducedWidth C (S \ {m}) ≤ inducedWidth C S :=
    Dilworth.inducedWidth_mono C _ _ Finset.sdiff_subset
  have heq : inducedWidth C (S \ {m}) = inducedWidth C S := le_antisymm hmono hle
  obtain ⟨B, hBS', hBanti, hBcard⟩ := exists_max_antichain C (S \ {m}) (by omega)
  have hmB := h_in_every B (Finset.Subset.trans hBS' Finset.sdiff_subset) hBanti (by omega)
  exact absurd hmB (by
    intro hmB'; have := hBS' hmB'
    rw [Finset.mem_sdiff] at this; exact this.2 (Finset.mem_singleton.mpr rfl))

/-! ### Pigeonhole: chain cover bounds width -/

/-- If S is covered by k chains (each a subset of S), then width(S) ≤ k. -/
theorem width_le_cover_card {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (chains : Finset (Finset C.Λ))
    (hchains : ∀ L ∈ chains, IsChainFS C L)
    (hcover : ∀ x ∈ S, ∃ L ∈ chains, x ∈ L) :
    inducedWidth C S ≤ chains.card := by
  unfold inducedWidth
  apply Finset.sup_le
  intro B hB_mem
  split_ifs with hBanti
  · -- B is an antichain in S. Each b ∈ B is in some chain L.
    -- Two elements of B can't share a chain (antichain vs chain).
    -- So |B| ≤ |chains| by a counting argument.
    have hBS := Finset.mem_powerset.mp hB_mem
    -- For each chain L, B ∩ L has ≤ 1 element
    have hone : ∀ L ∈ chains, (B.filter (fun b => b ∈ L)).card ≤ 1 := by
      intro L hL
      by_contra hgt; push_neg at hgt
      have hne : (B.filter (fun b => b ∈ L)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro hempty
        rw [hempty, Finset.card_empty] at hgt; omega
      obtain ⟨a, ha⟩ := hne
      rw [Finset.mem_filter] at ha
      have : ∃ b ∈ B.filter (fun b => b ∈ L), b ≠ a := by
        by_contra h'; push_neg at h'
        have : B.filter (fun b => b ∈ L) ⊆ {a} := fun x hx => Finset.mem_singleton.mpr (h' x hx)
        have := Finset.card_le_card this; simp at this; omega
      obtain ⟨b, hb, hab⟩ := this
      rw [Finset.mem_filter] at hb
      have hchain := hchains L hL
      rcases hchain a ha.2 b hb.2 with hle | hle
      · exact (hBanti a ha.1 b hb.1 (Ne.symm hab)).1 hle
      · exact (hBanti a ha.1 b hb.1 (Ne.symm hab)).2 hle
    calc B.card
        ≤ (chains.biUnion (fun L => B.filter (fun b => b ∈ L))).card := by
          apply Finset.card_le_card
          intro b hb
          rw [Finset.mem_biUnion]
          obtain ⟨L, hL, hbL⟩ := hcover b (hBS hb)
          exact ⟨L, hL, Finset.mem_filter.mpr ⟨hb, hbL⟩⟩
      _ ≤ chains.sum (fun L => (B.filter (fun b => b ∈ L)).card) :=
          Finset.card_biUnion_le
      _ ≤ chains.sum (fun _ => 1) := Finset.sum_le_sum hone
      _ = chains.card := by simp
  · exact Nat.zero_le _

/-! ### Full chain cover (Dilworth decomposition) -/

/-- **Full Dilworth cover**: S can be covered by ≤ inducedWidth(S) chains,
    each a subset of S.

    Proved by strong induction on |S|:
    - |S| = width: singleton chains (S is antichain).
    - |S| > width, universal element: remove it, IH, add {m}.
    - |S| > width, no universal element: C+/C- merge (sorry). -/
theorem dilworth_full_cover {k : Type*} [Field k] (C : CAlg k) :
    ∀ (n : ℕ) (S : Finset C.Λ), S.card ≤ n →
    ∃ chains : Finset (Finset C.Λ),
      (∀ L ∈ chains, L ⊆ S ∧ IsChainFS C L) ∧
      (∀ x ∈ S, ∃ L ∈ chains, x ∈ L) ∧
      chains.card ≤ inducedWidth C S := by
  intro n
  induction n with
  | zero =>
    intro S hS
    have : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    exact ⟨∅, fun _ h => absurd h (by simp), fun x hx => absurd (this ▸ hx) (by simp), Nat.zero_le _⟩
  | succ n ih =>
    intro S hScard
    by_cases hS_empty : S = ∅
    · exact ⟨∅, fun _ h => absurd h (by simp), fun x hx => absurd (hS_empty ▸ hx) (by simp), Nat.zero_le _⟩
    have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    have hS_w : inducedWidth C S > 0 := by
      obtain ⟨x, hx⟩ := hS_ne
      have hanti_sing : IsAntichain C ({x} : Finset C.Λ) := by
        intro a ha b hb hab
        simp only [Finset.mem_singleton] at ha hb
        subst ha; subst hb; exact absurd rfl hab
      have : 1 ≤ inducedWidth C S :=
        antichain_card_le_inducedWidth C S _ (Finset.singleton_subset_iff.mpr hx) hanti_sing
      simp at this; omega
    -- Case 1: |S| = width(S) → S is antichain
    by_cases hcard : S.card = inducedWidth C S
    · have hanti : IsAntichain C S := by
        by_contra hna
        have : inducedWidth C S < S.card := by
          unfold inducedWidth
          rw [Finset.sup_lt_iff (by omega : (0 : ℕ) < S.card)]
          intro A hA_mem; split_ifs with hAC
          · by_contra hle; push_neg at hle
            exact hna (Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hA_mem) hle ▸ hAC)
          · omega
        omega
      refine ⟨S.image (fun x => ({x} : Finset C.Λ)), ?_, ?_, ?_⟩
      · intro L hL
        simp only [Finset.mem_image] at hL; obtain ⟨x, hx, rfl⟩ := hL
        exact ⟨Finset.singleton_subset_iff.mpr hx,
          fun a ha b hb => by simp at ha hb; rw [ha, hb]; left; exact C.le_refl _⟩
      · intro x hx
        exact ⟨{x}, Finset.mem_image.mpr ⟨x, hx, rfl⟩, Finset.mem_singleton.mpr rfl⟩
      · calc (S.image _).card ≤ S.card := Finset.card_image_le
          _ = inducedWidth C S := hcard
    -- Case 2: |S| > width(S)
    have hS_gt : S.card > inducedWidth C S := by
      have := inducedWidth_le_card C S; omega
    -- Sub-case 2a: ∃ element in every max antichain
    by_cases h_univ : ∃ m ∈ S, ∀ B : Finset C.Λ, B ⊆ S → IsAntichain C B →
      B.card = inducedWidth C S → m ∈ B
    · obtain ⟨m, hm, hm_univ⟩ := h_univ
      have hw_dec := width_decreases_when_in_every_antichain C S m hS_w hm_univ
      have hcard_le : (S \ {m}).card ≤ n := by
        have : (S \ {m}).card < S.card := by
          apply Finset.card_lt_card
          exact ⟨Finset.sdiff_subset, fun h =>
            absurd (Finset.mem_singleton.mpr rfl) (Finset.mem_sdiff.mp (h hm)).2⟩
        omega
      obtain ⟨chains', hch', hcov', hcard'⟩ := ih (S \ {m}) hcard_le
      refine ⟨insert {m} chains', ?_, ?_, ?_⟩
      · intro L hL
        rw [Finset.mem_insert] at hL
        rcases hL with rfl | hL
        · exact ⟨Finset.singleton_subset_iff.mpr hm,
            fun a ha b hb => by simp at ha hb; rw [ha, hb]; left; exact C.le_refl _⟩
        · obtain ⟨hLS, hLchain⟩ := hch' L hL
          exact ⟨Finset.Subset.trans hLS Finset.sdiff_subset, hLchain⟩
      · intro x hx
        by_cases hxm : x = m
        · exact ⟨{m}, Finset.mem_insert_self _ _, hxm ▸ Finset.mem_singleton.mpr rfl⟩
        · obtain ⟨L, hL, hxL⟩ := hcov' x (Finset.mem_sdiff.mpr ⟨hx, Finset.mem_singleton.not.mpr hxm⟩)
          exact ⟨L, Finset.mem_insert.mpr (Or.inr hL), hxL⟩
      · calc (insert {m} chains').card
            ≤ chains'.card + 1 := Finset.card_insert_le _ _
          _ ≤ inducedWidth C (S \ {m}) + 1 := by omega
          _ ≤ inducedWidth C S := by omega
    · -- Sub-case 2b: no element is in every max antichain.
      -- Standard proof: C+/C- decomposition + merge at the max antichain A.
      -- Define C+ = {x ∈ S : ∃ a ∈ A, a ≤ x}, C- = {x ∈ S : ∃ a ∈ A, x ≤ a}.
      -- Then C+ ∪ C- = S, A ⊆ C+ ∩ C-, and ¬(C+ = S ∧ C- = S).
      -- At least one of C+, C- is a proper subset of S with width = w.
      -- Apply IH to both (or to the proper one(s)), get w chains each.
      -- Each a ∈ A appears in exactly one chain from each cover.
      -- Merge: pair the C+-chain and C--chain meeting at each a ∈ A.
      -- The merged chain is valid since C--elements ≤ a ≤ C+-elements.
      -- This gives w chains covering S.
      --
      -- The merge step requires showing the chain matching at A is
      -- a bijection (each chain has exactly one A-element, by the
      -- antichain-chain intersection bound). When only one of C+, C-
      -- is proper, the extension requires a Hall-type matching argument
      -- between the cover chains and A.
      --
      -- Full formalization requires ~300 lines (Hall's matching theorem
      -- or an equivalent combinatorial argument). This is the single
      -- remaining sorry in the causal algebraic geometry codebase.
      sorry

/-! ### The Dilworth inductive step -/

/-- **Dilworth inductive step**: For any nonempty S with inducedWidth(S) > 0,
    there exists a chain L ⊆ S such that inducedWidth(S \ L) < inducedWidth(S).

    Follows from `dilworth_full_cover` and `width_le_cover_card`. -/
theorem dilworth_inductive_step {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (hne : S.Nonempty) (hw : inducedWidth C S > 0) :
    ∃ L : Finset C.Λ, L ⊆ S ∧ IsChainFS C L ∧ L.Nonempty ∧
      inducedWidth C (S \ L) < inducedWidth C S := by
  obtain ⟨chains, hch, hcov, hcard⟩ := dilworth_full_cover C S.card S (le_refl _)
  -- Pick a chain containing some element of S
  obtain ⟨x, hx⟩ := hne
  obtain ⟨L, hL_mem, hxL⟩ := hcov x hx
  obtain ⟨hLS, hLchain⟩ := hch L hL_mem
  refine ⟨L, hLS, hLchain, ⟨x, hxL⟩, ?_⟩
  -- The remaining chains cover S \ L
  have hcov' : ∀ y ∈ S \ L, ∃ M ∈ chains.erase L, y ∈ M := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨M, hM, hyM⟩ := hcov y hy.1
    have hML : M ≠ L := by
      intro heq; rw [heq] at hyM; exact hy.2 hyM
    exact ⟨M, Finset.mem_erase.mpr ⟨hML, hM⟩, hyM⟩
  -- So width(S \ L) ≤ |chains \ {L}| = |chains| - 1
  have hch' : ∀ M ∈ chains.erase L, IsChainFS C M := by
    intro M hM; exact (hch M (Finset.mem_erase.mp hM).2).2
  have hwidth : inducedWidth C (S \ L) ≤ (chains.erase L).card :=
    width_le_cover_card C (S \ L) (chains.erase L) hch' hcov'
  have herase_card : (chains.erase L).card = chains.card - 1 :=
    Finset.card_erase_of_mem hL_mem
  -- chains.card ≤ w, so (chains.erase L).card ≤ w - 1
  -- width(S \ L) ≤ w - 1 < w
  have hchains_pos : chains.card ≥ 1 := by
    have : chains.Nonempty := ⟨L, hL_mem⟩
    exact Finset.Nonempty.card_pos this
  omega

/-- The Dilworth inductive step, packaged for `dilworth_from_inductive_step`. -/
theorem dilworth_step_hypothesis {k : Type*} [Field k] (C : CAlg k) :
    ∀ (S : Finset C.Λ), S.Nonempty → inducedWidth C S > 0 →
      ∃ (L : Finset C.Λ), L ⊆ S ∧ IsChainFS C L ∧ L.Nonempty ∧
        inducedWidth C (S \ L) < inducedWidth C S :=
  fun S hne hw => dilworth_inductive_step C S hne hw

/-- **Dilworth's theorem (complete)**: every finite poset of width w
    can be partitioned into w chains. -/
theorem dilworth_theorem {k : Type*} [Field k] (C : CAlg k) :
    ∃ chains : Finset (Finset C.Λ),
      IsChainCover C chains ∧ chains.card ≤ width C :=
  dilworth_from_inductive_step C (dilworth_step_hypothesis C)

end CausalAlgebraicGeometry.DilworthProof
