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

  Zero sorry. Zero custom axioms.
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

/-! ### Minimal and maximal elements -/

/-- An element is minimal in S if no strictly smaller element exists in S. -/
def IsMinimalIn {k : Type*} [Field k] (C : CAlg k) (S : Finset C.Λ) (x : C.Λ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, C.le y x → y = x

/-- An element is maximal in S if no strictly larger element exists in S. -/
def IsMaximalIn {k : Type*} [Field k] (C : CAlg k) (S : Finset C.Λ) (x : C.Λ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, C.le x y → y = x

/-- Every nonempty finite set has a minimal element (by strong induction on subsets). -/
theorem exists_minimal {k : Type*} [Field k] (C : CAlg k) (S : Finset C.Λ)
    (hne : S.Nonempty) : ∃ m, IsMinimalIn C S m := by
  suffices ∀ (T : Finset C.Λ), T ⊆ S → T.Nonempty →
      ∃ m ∈ T, ∀ y ∈ T, C.le y m → y = m from by
    obtain ⟨m, hm, hmin⟩ := this S (le_refl S) hne
    exact ⟨m, hm, hmin⟩
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hTS hTne
    obtain ⟨x, hx⟩ := hTne
    by_cases hmin : ∀ y ∈ T, C.le y x → y = x
    · exact ⟨x, hx, hmin⟩
    · push_neg at hmin
      obtain ⟨y, hyT, hle, hne⟩ := hmin
      set T' := T.filter (fun z => C.le z x)
      set T'' := T' \ {x}
      have hyT'' : y ∈ T'' :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hyT, hle⟩, Finset.mem_singleton.not.mpr hne⟩
      have hT''_sub : T'' ⊂ T := by
        constructor
        · intro z hz; exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
        · intro hsub
          exact (Finset.mem_sdiff.mp (hsub hx)).2 (Finset.mem_singleton.mpr rfl)
      obtain ⟨m, hm, hmin⟩ := ih T'' hT''_sub
        (fun z hz => hTS ((Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1)) ⟨y, hyT''⟩
      refine ⟨m, (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).1, fun z hz hlez => ?_⟩
      by_cases hzx : z = x
      · have hm_sdiff := Finset.mem_sdiff.mp hm
        have hm_filt := Finset.mem_filter.mp hm_sdiff.1
        have hmz : C.le m z := hzx ▸ hm_filt.2
        exact absurd (C.le_antisymm m z hmz hlez)
          (fun heq => hm_sdiff.2 (Finset.mem_singleton.mpr (hzx ▸ heq)))
      · have hm_filt := Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1
        exact hmin z (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hz, C.le_trans z m x hlez hm_filt.2⟩,
          Finset.mem_singleton.not.mpr hzx⟩) hlez

/-- Every nonempty finite set has a maximal element (by strong induction on subsets). -/
theorem exists_maximal {k : Type*} [Field k] (C : CAlg k) (S : Finset C.Λ)
    (hne : S.Nonempty) : ∃ m, IsMaximalIn C S m := by
  suffices ∀ (T : Finset C.Λ), T ⊆ S → T.Nonempty →
      ∃ m ∈ T, ∀ y ∈ T, C.le m y → y = m from by
    obtain ⟨m, hm, hmax⟩ := this S (le_refl S) hne
    exact ⟨m, hm, hmax⟩
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hTS hTne
    obtain ⟨x, hx⟩ := hTne
    by_cases hmax : ∀ y ∈ T, C.le x y → y = x
    · exact ⟨x, hx, hmax⟩
    · push_neg at hmax
      obtain ⟨y, hyT, hle, hne⟩ := hmax
      set T' := T.filter (fun z => C.le x z)
      set T'' := T' \ {x}
      have hyT'' : y ∈ T'' :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hyT, hle⟩, Finset.mem_singleton.not.mpr hne⟩
      have hT''_sub : T'' ⊂ T := by
        constructor
        · intro z hz; exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
        · intro hsub
          exact (Finset.mem_sdiff.mp (hsub hx)).2 (Finset.mem_singleton.mpr rfl)
      obtain ⟨m, hm, hmax⟩ := ih T'' hT''_sub
        (fun z hz => hTS ((Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1)) ⟨y, hyT''⟩
      refine ⟨m, (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).1, fun z hz hlez => ?_⟩
      by_cases hzx : z = x
      · have hm_sdiff := Finset.mem_sdiff.mp hm
        have hm_filt := Finset.mem_filter.mp hm_sdiff.1
        -- hm_filt.2 : C.le x m, hlez : C.le m z, hzx : z = x
        -- So C.le m x (from hzx ▸ hlez). With C.le x m: m = x. But m ∉ {x}. Contradiction.
        have hmx : C.le m x := hzx ▸ hlez
        exact absurd (C.le_antisymm m x hmx hm_filt.2)
          (fun heq => hm_sdiff.2 (Finset.mem_singleton.mpr heq))
      · have hm_filt := Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1
        exact hmax z (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hz, C.le_trans x m z hm_filt.2 hlez⟩,
          Finset.mem_singleton.not.mpr hzx⟩) hlez

/-- In Case 2b (no universal element), there exists a max antichain that
    does NOT contain all minimal elements of S. -/
theorem exists_max_antichain_not_all_minimals {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (hne : S.Nonempty) (hw : inducedWidth C S > 0)
    (h_no_univ : ¬∃ m ∈ S, ∀ B : Finset C.Λ, B ⊆ S → IsAntichain C B →
      B.card = inducedWidth C S → m ∈ B) :
    ∃ A : Finset C.Λ, A ⊆ S ∧ IsAntichain C A ∧ A.card = inducedWidth C S ∧
      ∃ m, IsMinimalIn C S m ∧ m ∉ A := by
  by_contra hall
  push_neg at hall
  -- Every max antichain contains every minimal
  have h_all : ∀ A : Finset C.Λ, A ⊆ S → IsAntichain C A → A.card = inducedWidth C S →
      ∀ m, IsMinimalIn C S m → m ∈ A := by
    intro A hAS hA hAcard m hm
    exact hall A hAS hA hAcard m hm
  -- Pick any max antichain A₀
  obtain ⟨A₀, hA₀S, hA₀anti, hA₀card⟩ := exists_max_antichain C S hw
  -- Pick any minimal m₀
  obtain ⟨m₀, hm₀⟩ := exists_minimal C S hne
  -- m₀ is in every max antichain
  have hm₀_univ : ∀ B : Finset C.Λ, B ⊆ S → IsAntichain C B →
      B.card = inducedWidth C S → m₀ ∈ B := by
    intro B hBS hBanti hBcard
    exact h_all B hBS hBanti hBcard m₀ hm₀
  -- So m₀ is universal, contradicting h_no_univ
  exact h_no_univ ⟨m₀, hm₀.1, hm₀_univ⟩

/-- In Case 2b, there exists a max antichain that does NOT contain all maximal elements. -/
theorem exists_max_antichain_not_all_maximals {k : Type*} [Field k] (C : CAlg k)
    (S : Finset C.Λ) (hne : S.Nonempty) (hw : inducedWidth C S > 0)
    (h_no_univ : ¬∃ m ∈ S, ∀ B : Finset C.Λ, B ⊆ S → IsAntichain C B →
      B.card = inducedWidth C S → m ∈ B) :
    ∃ A : Finset C.Λ, A ⊆ S ∧ IsAntichain C A ∧ A.card = inducedWidth C S ∧
      ∃ m, IsMaximalIn C S m ∧ m ∉ A := by
  by_contra hall
  push_neg at hall
  have h_all : ∀ A : Finset C.Λ, A ⊆ S → IsAntichain C A → A.card = inducedWidth C S →
      ∀ m, IsMaximalIn C S m → m ∈ A := by
    intro A hAS hA hAcard m hm
    exact hall A hAS hA hAcard m hm
  obtain ⟨M₀, hM₀⟩ := exists_maximal C S hne
  have hM₀_univ : ∀ B : Finset C.Λ, B ⊆ S → IsAntichain C B →
      B.card = inducedWidth C S → M₀ ∈ B := by
    intro B hBS hBanti hBcard
    exact h_all B hBS hBanti hBcard M₀ hM₀
  exact h_no_univ ⟨M₀, hM₀.1, hM₀_univ⟩

/-! ### C+/C- decomposition helpers -/

/-- C+ = {x ∈ S : ∃ a ∈ A, a ≤ x} -/
def cPlus {k : Type*} [Field k] (C : CAlg k) (S A : Finset C.Λ) : Finset C.Λ :=
  S.filter (fun x => ∃ a ∈ A, C.le a x)

/-- C- = {x ∈ S : ∃ a ∈ A, x ≤ a} -/
def cMinus {k : Type*} [Field k] (C : CAlg k) (S A : Finset C.Λ) : Finset C.Λ :=
  S.filter (fun x => ∃ a ∈ A, C.le x a)

theorem cPlus_subset {k : Type*} [Field k] (C : CAlg k) (S A : Finset C.Λ) :
    cPlus C S A ⊆ S := Finset.filter_subset _ _

theorem cMinus_subset {k : Type*} [Field k] (C : CAlg k) (S A : Finset C.Λ) :
    cMinus C S A ⊆ S := Finset.filter_subset _ _

theorem antichain_subset_cPlus {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) : A ⊆ cPlus C S A := by
  intro a ha
  simp only [cPlus, Finset.mem_filter]
  exact ⟨hAS ha, a, ha, C.le_refl a⟩

theorem antichain_subset_cMinus {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) : A ⊆ cMinus C S A := by
  intro a ha
  simp only [cMinus, Finset.mem_filter]
  exact ⟨hAS ha, a, ha, C.le_refl a⟩

/-- C+ ∪ C- = S when A is a max antichain (every x ∈ S is comparable to some a ∈ A). -/
theorem cPlus_union_cMinus {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hAmax : A.card = inducedWidth C S) :
    cPlus C S A ∪ cMinus C S A = S := by
  ext x; constructor
  · intro hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact cPlus_subset C S A hx
    · exact cMinus_subset C S A hx
  · intro hx
    rw [Finset.mem_union]
    by_cases hxA : x ∈ A
    · left; exact antichain_subset_cPlus C S A hAS hxA
    · obtain ⟨a, ha, hcomp⟩ := comparable_to_max_antichain C S A hAS hA hAmax x hx hxA
      rcases hcomp with hax | hxa
      · left; simp only [cPlus, Finset.mem_filter]; exact ⟨hx, a, ha, hax⟩
      · right; simp only [cMinus, Finset.mem_filter]; exact ⟨hx, a, ha, hxa⟩

/-- If A is a max antichain not containing all minimals, then C+ ⊊ S. -/
theorem cPlus_ssubset {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hAmax : A.card = inducedWidth C S)
    (m : C.Λ) (hm : IsMinimalIn C S m) (hmA : m ∉ A) :
    cPlus C S A ⊂ S := by
  constructor
  · exact cPlus_subset C S A
  · intro h
    -- m ∈ S, so m ∈ cPlus C S A
    have hmS := hm.1
    have hmc := h hmS
    simp only [cPlus, Finset.mem_filter] at hmc
    obtain ⟨_, a, ha, ham⟩ := hmc
    -- a ≤ m with a ∈ A ⊆ S and m minimal → a = m
    have := hm.2 a (hAS ha) ham
    -- a = m, but m ∉ A and a ∈ A, contradiction
    exact hmA (this ▸ ha)

/-- If A is a max antichain not containing all maximals, then C- ⊊ S. -/
theorem cMinus_ssubset {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hAmax : A.card = inducedWidth C S)
    (M : C.Λ) (hM : IsMaximalIn C S M) (hMA : M ∉ A) :
    cMinus C S A ⊂ S := by
  constructor
  · exact cMinus_subset C S A
  · intro h
    have hMS := hM.1
    have hMc := h hMS
    simp only [cMinus, Finset.mem_filter] at hMc
    obtain ⟨_, a, ha, hMa⟩ := hMc
    have := hM.2 a (hAS ha) hMa
    exact hMA (this ▸ ha)

/-- Width of C+ ≥ w (since A ⊆ C+). -/
theorem width_cPlus_ge {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hAmax : A.card = inducedWidth C S) :
    inducedWidth C (cPlus C S A) ≥ inducedWidth C S := by
  calc inducedWidth C S = A.card := hAmax.symm
    _ ≤ inducedWidth C (cPlus C S A) :=
        antichain_card_le_inducedWidth C _ A (antichain_subset_cPlus C S A hAS) hA

/-- Width of C- ≥ w (since A ⊆ C-). -/
theorem width_cMinus_ge {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hAmax : A.card = inducedWidth C S) :
    inducedWidth C (cMinus C S A) ≥ inducedWidth C S := by
  calc inducedWidth C S = A.card := hAmax.symm
    _ ≤ inducedWidth C (cMinus C S A) :=
        antichain_card_le_inducedWidth C _ A (antichain_subset_cMinus C S A hAS) hA

/-- Width of C+ = w. -/
theorem width_cPlus_eq {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hAmax : A.card = inducedWidth C S) :
    inducedWidth C (cPlus C S A) = inducedWidth C S := by
  apply le_antisymm
  · exact inducedWidth_mono C _ _ (cPlus_subset C S A)
  · exact width_cPlus_ge C S A hAS hA hAmax

/-- Width of C- = w. -/
theorem width_cMinus_eq {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hAmax : A.card = inducedWidth C S) :
    inducedWidth C (cMinus C S A) = inducedWidth C S := by
  apply le_antisymm
  · exact inducedWidth_mono C _ _ (cMinus_subset C S A)
  · exact width_cMinus_ge C S A hAS hA hAmax

/-! ### Chain-antichain intersection -/

/-- A chain and an antichain intersect in at most 1 element. -/
theorem chain_antichain_inter_card_le_one {k : Type*} [Field k] (C : CAlg k)
    (L A : Finset C.Λ) (hL : IsChainFS C L) (hA : IsAntichain C A) :
    (L ∩ A).card ≤ 1 := by
  by_contra h
  push_neg at h
  -- ≥ 2 elements in L ∩ A
  have hne : (L ∩ A).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro he; rw [he, Finset.card_empty] at h; omega
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_inter] at hx
  have : ∃ y ∈ L ∩ A, y ≠ x := by
    by_contra h'; push_neg at h'
    have : L ∩ A ⊆ {x} := fun z hz => Finset.mem_singleton.mpr (h' z hz)
    have := Finset.card_le_card this; simp at this; omega
  obtain ⟨y, hy, hne⟩ := this
  rw [Finset.mem_inter] at hy
  -- x, y ∈ L (chain) → comparable; x, y ∈ A (antichain) → incomparable. Contradiction.
  rcases hL x hx.1 y hy.1 with hxy | hyx
  · exact (hA x hx.2 y hy.2 hne.symm).1 hxy
  · exact (hA x hx.2 y hy.2 hne.symm).2 hyx

/-- If w chains cover a set containing an antichain A of size w,
    each chain contains exactly one element of A. -/
theorem chain_cover_antichain_bijection {k : Type*} [Field k] (C : CAlg k)
    (A : Finset C.Λ) (T : Finset C.Λ) (hAT : A ⊆ T)
    (hA : IsAntichain C A)
    (chains : Finset (Finset C.Λ))
    (hchains : ∀ L ∈ chains, IsChainFS C L)
    (hcover : ∀ x ∈ T, ∃ L ∈ chains, x ∈ L)
    (hcard : chains.card ≤ A.card) :
    ∀ L ∈ chains, ∃! a, a ∈ A ∧ a ∈ L := by
  -- Each a ∈ A is in some chain. Two A-elements can't share a chain.
  -- So we need |A| distinct chains, but |chains| ≤ |A|, so each chain has exactly one.
  -- First: each chain has ≤ 1 A-element (chain ∩ antichain ≤ 1)
  have h_le_one : ∀ L ∈ chains, (A.filter (fun a => a ∈ L)).card ≤ 1 := by
    intro L hL
    have hAL_eq : A.filter (fun a => a ∈ L) = A ∩ L := by
      ext x; simp [Finset.mem_filter, Finset.mem_inter]
    rw [hAL_eq, Finset.inter_comm]
    exact chain_antichain_inter_card_le_one C L A (hchains L hL) hA
  -- Each a ∈ A is in some chain
  have h_exists : ∀ a ∈ A, ∃ L ∈ chains, a ∈ L := fun a ha => hcover a (hAT ha)
  -- Count: |A| ≤ ∑_{L ∈ chains} |A ∩ L| ≤ |chains| · 1 ≤ |A|
  -- So every inequality is equality, meaning each chain has exactly 1.
  have h_sum_ge : A.card ≤ chains.sum (fun L => (A.filter (fun a => a ∈ L)).card) := by
    calc A.card
        ≤ (chains.biUnion (fun L => A.filter (fun a => a ∈ L))).card := by
          apply Finset.card_le_card
          intro a ha
          rw [Finset.mem_biUnion]
          obtain ⟨L, hL, haL⟩ := h_exists a ha
          exact ⟨L, hL, Finset.mem_filter.mpr ⟨ha, haL⟩⟩
      _ ≤ chains.sum (fun L => (A.filter (fun a => a ∈ L)).card) :=
          Finset.card_biUnion_le
  have h_sum_le : chains.sum (fun L => (A.filter (fun a => a ∈ L)).card) ≤ chains.card := by
    calc chains.sum (fun L => (A.filter (fun a => a ∈ L)).card)
        ≤ chains.sum (fun _ => 1) := Finset.sum_le_sum h_le_one
      _ = chains.card := by simp
  -- So each term is exactly 1
  have h_each_eq_one : ∀ L ∈ chains, (A.filter (fun a => a ∈ L)).card = 1 := by
    by_contra hcontra
    push_neg at hcontra
    obtain ⟨L, hL, hne⟩ := hcontra
    have hle := h_le_one L hL
    have hzero : (A.filter (fun a => a ∈ L)).card = 0 := by omega
    -- f(L) + sum_{chains \ L} f = sum_chains f
    have hsplit := Finset.add_sum_erase chains (fun L => (A.filter (fun a => a ∈ L)).card) hL
    -- sum_chains f ≥ A.card (from h_sum_ge) and sum_chains f ≤ chains.card (from h_sum_le)
    -- After removing L: sum = sum_chains f - 0 = sum_chains f
    -- But also sum_{chains\L} ≤ |chains\L| = |chains| - 1
    simp only [] at hsplit
    rw [hzero, zero_add] at hsplit
    have hsub : (chains.erase L).sum (fun L => (A.filter (fun a => a ∈ L)).card) ≤ (chains.erase L).card := by
      apply le_trans (Finset.sum_le_sum (fun M hM => h_le_one M (Finset.mem_erase.mp hM).2))
      simp
    have herase := Finset.card_erase_of_mem hL
    -- hsplit : erase_sum = full_sum
    -- h_sum_ge : A.card ≤ full_sum
    -- hcard : chains.card ≤ A.card
    -- hsub : erase_sum ≤ erase_card = chains.card - 1
    have : A.card ≤ (chains.erase L).sum (fun L => (A.filter (fun a => a ∈ L)).card) := by
      rw [hsplit]; exact h_sum_ge
    have hchains_pos : 0 < chains.card := by
      exact Finset.Nonempty.card_pos ⟨L, hL⟩
    omega
  -- Now convert "card = 1" to "exists unique"
  intro L hL
  have h1 := h_each_eq_one L hL
  rw [Finset.card_eq_one] at h1
  obtain ⟨a, ha⟩ := h1
  have haL : a ∈ A.filter (fun a => a ∈ L) := ha ▸ Finset.mem_singleton.mpr rfl
  rw [Finset.mem_filter] at haL
  exact ⟨a, ⟨haL.1, haL.2⟩, fun b ⟨hbA, hbL⟩ => by
    have hb : b ∈ A.filter (fun a => a ∈ L) := Finset.mem_filter.mpr ⟨hbA, hbL⟩
    rw [ha] at hb; exact Finset.mem_singleton.mp hb⟩

/-! ### Chain merging -/

/-- Elements of C- are ≤ their A-representative, elements of C+ are ≥ their A-representative.
    So merging a C- chain piece (below a) with a C+ chain piece (above a) gives a chain. -/
theorem merge_is_chain {k : Type*} [Field k] (C : CAlg k)
    (L₁ L₂ : Finset C.Λ) (a : C.Λ)
    (hL₁ : IsChainFS C L₁) (hL₂ : IsChainFS C L₂)
    (h₁ : ∀ x ∈ L₁, C.le x a) (h₂ : ∀ x ∈ L₂, C.le a x) :
    IsChainFS C (L₁ ∪ L₂) := by
  intro x hx y hy
  rw [Finset.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hL₁ x hx y hy
  · left; exact C.le_trans x a y (h₁ x hx) (h₂ y hy)
  · right; exact C.le_trans y a x (h₁ y hy) (h₂ x hx)
  · exact hL₂ x hx y hy

/-! ### Orientation lemmas for chains meeting A -/

/-- In C-(A), if L is a chain meeting A at exactly {a}, then every x ∈ L satisfies x ≤ a.
    Proof: x ∈ L ⊆ C-(A), so x ≤ some a' ∈ A. L is a chain with a ∈ L,
    so x and a are comparable. If a ≤ x, then a ≤ x ≤ a', so (if a ≠ a') a < a',
    contradicting A antichain. So a = a' and a ≤ x ≤ a gives x = a. -/
theorem cMinus_chain_all_le_rep {k : Type*} [Field k] (C : CAlg k)
    (S A L : Finset C.Λ) (a : C.Λ) (hA : IsAntichain C A) (hAS : A ⊆ S)
    (hL_chain : IsChainFS C L) (hL_sub : L ⊆ cMinus C S A) (haL : a ∈ L) (haA : a ∈ A)
    (h_unique : ∀ b, b ∈ A ∧ b ∈ L → b = a) :
    ∀ x ∈ L, C.le x a := by
  intro x hx
  have hx_cm : x ∈ cMinus C S A := hL_sub hx
  simp only [cMinus, Finset.mem_filter] at hx_cm
  obtain ⟨_, a', ha', hxa'⟩ := hx_cm
  rcases hL_chain x hx a haL with hxa | hax
  · -- x ≤ a: done
    exact hxa
  · -- a ≤ x: then a ≤ x ≤ a'. If a ≠ a', then a < a' contradicts A antichain.
    -- So a = a', and a ≤ x ≤ a gives x = a, so x ≤ a.
    by_cases haa' : a = a'
    · rw [← haa'] at hxa'; exact hxa'
    · -- a < a': both in A antichain → contradiction
      exfalso
      have : ¬ C.le a a' ∧ ¬ C.le a' a := hA a haA a' ha' haa'
      exact this.1 (C.le_trans a x a' hax hxa')

/-- In C+(A), if L is a chain meeting A at exactly {a}, then every x ∈ L satisfies a ≤ x. -/
theorem cPlus_chain_all_ge_rep {k : Type*} [Field k] (C : CAlg k)
    (S A L : Finset C.Λ) (a : C.Λ) (hA : IsAntichain C A) (hAS : A ⊆ S)
    (hL_chain : IsChainFS C L) (hL_sub : L ⊆ cPlus C S A) (haL : a ∈ L) (haA : a ∈ A)
    (h_unique : ∀ b, b ∈ A ∧ b ∈ L → b = a) :
    ∀ x ∈ L, C.le a x := by
  intro x hx
  have hx_cp : x ∈ cPlus C S A := hL_sub hx
  simp only [cPlus, Finset.mem_filter] at hx_cp
  obtain ⟨_, a', ha', ha'x⟩ := hx_cp
  rcases hL_chain x hx a haL with hxa | hax
  · -- x ≤ a: then a' ≤ x ≤ a. If a' ≠ a, then a' < a contradicts A antichain.
    by_cases haa' : a = a'
    · rw [← haa'] at ha'x; exact ha'x
    · exfalso
      have : ¬ C.le a' a ∧ ¬ C.le a a' := hA a' ha' a haA (fun h => haa' h.symm)
      exact this.1 (C.le_trans a' x a ha'x hxa)
  · exact hax

/-- If C+(A) = S and A is a max antichain, then every element of A is minimal in S. -/
theorem cPlus_eq_implies_A_all_minimal {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hcp_eq : cPlus C S A = S) :
    ∀ a ∈ A, IsMinimalIn C S a := by
  intro a ha
  refine ⟨hAS ha, fun y hy hya => ?_⟩
  -- y ∈ S = C+(A), so ∃ a' ∈ A with a' ≤ y
  have hy_cp : y ∈ cPlus C S A := by rw [hcp_eq]; exact hy
  simp only [cPlus, Finset.mem_filter] at hy_cp
  obtain ⟨_, a', ha', ha'y⟩ := hy_cp
  -- a' ≤ y ≤ a. If a' ≠ a, then a' < a contradicts A antichain.
  by_cases haa' : a = a'
  · -- a = a', so a' = a, a' ≤ y ≤ a = a', so y = a
    exact C.le_antisymm y a (hya) (haa' ▸ ha'y)
  · exfalso
    have : ¬ C.le a' a ∧ ¬ C.le a a' := hA a' ha' a ha (fun h => haa' h.symm)
    exact this.1 (C.le_trans a' y a ha'y hya)

/-- If C-(A) = S and A is a max antichain, then every element of A is maximal in S. -/
theorem cMinus_eq_implies_A_all_maximal {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hcm_eq : cMinus C S A = S) :
    ∀ a ∈ A, IsMaximalIn C S a := by
  intro a ha
  refine ⟨hAS ha, fun y hy hay => ?_⟩
  have hy_cm : y ∈ cMinus C S A := by rw [hcm_eq]; exact hy
  simp only [cMinus, Finset.mem_filter] at hy_cm
  obtain ⟨_, a', ha', hya'⟩ := hy_cm
  by_cases haa' : a = a'
  · rw [haa'] at hay ⊢
    exact C.le_antisymm y a' hya' hay
  · exfalso
    have : ¬ C.le a a' ∧ ¬ C.le a' a := hA a ha a' ha' haa'
    exact this.1 (C.le_trans a y a' hay hya')

/-- If every element of A is both minimal and maximal in S ("isolated"),
    and A is a max antichain of S with |S| > |A|, contradiction. -/
theorem no_isolated_antichain_covers {k : Type*} [Field k] (C : CAlg k)
    (S A : Finset C.Λ) (hAS : A ⊆ S) (hA : IsAntichain C A)
    (hAmax : A.card = inducedWidth C S)
    (h_iso : ∀ a ∈ A, IsMinimalIn C S a ∧ IsMaximalIn C S a)
    (hgt : S.card > inducedWidth C S) : False := by
  -- Every x ∈ S \ A is comparable to some a ∈ A (by comparable_to_max_antichain).
  -- But a is both minimal and maximal, so a ≤ x → a = x and x ≤ a → x = a.
  -- Either way x = a, contradicting x ∉ A.
  have hSA : S \ A ≠ ∅ := by
    intro h
    have : S ⊆ A := by
      intro x hx
      by_contra hxA
      have : x ∈ S \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
      rw [h] at this; simp at this
    have := Finset.card_le_card this
    omega
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hSA
  rw [Finset.mem_sdiff] at hx
  obtain ⟨a, ha, hcomp⟩ := comparable_to_max_antichain C S A hAS hA hAmax x hx.1 hx.2
  rcases hcomp with hax | hxa
  · -- a ≤ x, but a is maximal → x = a
    exact hx.2 ((h_iso a ha).2.2 x hx.1 hax ▸ ha)
  · -- x ≤ a, but a is minimal → x = a
    exact hx.2 ((h_iso a ha).1.2 x hx.1 hxa ▸ ha)

-- (The broken exists_good_antichain_UNUSED and helper code have been removed.
--  The C+/C- merge is now handled directly in dilworth_full_cover below.)
/- (exists_good_antichain and helper code removed - handled in dilworth_full_cover)
   -- Try A₁ (missing a minimal → C+ ⊊ S)
  obtain ⟨A₁, hA₁S, hA₁anti, hA₁card, m, hm_min, hm_notA₁⟩ :=
    exists_max_antichain_not_all_minimals C S hne hw h_no_univ
  have hcp₁ : cPlus C S A₁ ⊂ S := cPlus_ssubset C S A₁ hA₁S hA₁anti hA₁card m hm_min hm_notA₁
  -- Check if C-(A₁) ⊊ S
  by_cases hcm₁ : cMinus C S A₁ ⊂ S
  · exact ⟨A₁, hA₁S, hA₁anti, hA₁card, hcp₁, hcm₁⟩
  · -- C-(A₁) = S (it's ⊆ S always, and not ⊂, so =)
    have hcm₁_eq : cMinus C S A₁ = S := by
      rw [Finset.ssubset_iff_subset_ne] at hcm₁; push_neg at hcm₁
      exact (hcm₁ (cMinus_subset C S A₁)).symm
    -- So every element of A₁ is maximal
    have hA₁_max : ∀ a ∈ A₁, IsMaximalIn C S a :=
      cMinus_eq_implies_A_all_maximal C S A₁ hA₁S hA₁anti hcm₁_eq
    -- Try A₂ (missing a maximal → C- ⊊ S)
    obtain ⟨A₂, hA₂S, hA₂anti, hA₂card, M, hM_max, hM_notA₂⟩ :=
      exists_max_antichain_not_all_maximals C S hne hw h_no_univ
    have hcm₂ : cMinus C S A₂ ⊂ S := cMinus_ssubset C S A₂ hA₂S hA₂anti hA₂card M hM_max hM_notA₂
    -- Check if C+(A₂) ⊊ S
    by_cases hcp₂ : cPlus C S A₂ ⊂ S
    · exact ⟨A₂, hA₂S, hA₂anti, hA₂card, hcp₂, hcm₂⟩
    · -- C+(A₂) = S
      have hcp₂_eq : cPlus C S A₂ = S := by
        rw [Finset.ssubset_iff_subset_ne] at hcp₂; push_neg at hcp₂
        exact (hcp₂ (cPlus_subset C S A₂)).symm
      -- Every element of A₂ is minimal
      have hA₂_min : ∀ a ∈ A₂, IsMinimalIn C S a :=
        cPlus_eq_implies_A_all_minimal C S A₂ hA₂S hA₂anti hcp₂_eq
      -- A₁ = all maximals (each element is maximal), A₂ = all minimals (each element is minimal)
      -- Any a ∈ A₁ is maximal and in cPlus (= S via A₂), so a ≥ some a₂ ∈ A₂.
      -- a₂ is minimal, so a₂ ≤ a. If a₂ ≠ a, a₂ < a. a₂ is minimal.
      -- Similarly, a ∈ A₂ is minimal and in cMinus (= S via A₁), so a ≤ some a₁ ∈ A₁.
      -- a₁ is maximal, so a ≤ a₁. If a ≠ a₁, a < a₁.
      -- Any a₁ ∈ A₁: a₁ ∈ S = C+(A₂), so ∃ a₂ ∈ A₂ with a₂ ≤ a₁.
      -- a₂ minimal, a₁ maximal. If a₂ = a₁, then a₁ is both minimal and maximal.
      -- If a₂ ≠ a₁, then a₂ < a₁. Now a₁ is maximal → OK. a₂ is minimal → OK.
      -- Similarly for a₂ ∈ A₂: a₂ ∈ S = C-(A₁), so ∃ a₁ ∈ A₁ with a₂ ≤ a₁.

      -- We show every a ∈ A₁ is also minimal (hence isolated).
      -- a ∈ A₁ ⊆ S. Suppose b < a in S. b ∈ C+(A₂) = S, so ∃ a₂ ∈ A₂ with a₂ ≤ b.
      -- a₂ ≤ b < a. a₂ is minimal in S. Since a₂ ≤ b and a₂ ≤ a:
      -- A₁ is antichain, a ∈ A₁. Is a₂ ∈ A₁? a₂ ∈ A₂.
      -- Actually, a is maximal (a ∈ A₁). a ∈ S = C-(A₁), so ∃ a₁ ∈ A₁ with a ≤ a₁.
      -- Since a is maximal, a₁ = a. So a ≤ a. OK, that's trivial.
      -- Let's show a ∈ A₁ is minimal directly.
      -- Suppose y ∈ S, y ≤ a. y ∈ C+(A₂) = S, so ∃ a₂ ∈ A₂ with a₂ ≤ y.
      -- a₂ ≤ y ≤ a. a is maximal. a₂ is minimal.
      -- Now: a₂ ∈ A₂ and a ∈ A₁. a₂ ≤ a.
      -- If we can show a₂ = a, then since a₂ ≤ y ≤ a = a₂, y = a₂ = a. Done.
      -- a₂ ≤ a. a₂ minimal. Suppose a₂ ≠ a.
      -- a is in A₁, a₂ is in A₂. Are a and a₂ in the same antichain?
      -- No direct contradiction yet.

      -- Actually, we need a different approach. Let's show A₁ elements are isolated
      -- (both min and max) which contradicts |S| > w.
      have h_iso₁ : ∀ a ∈ A₁, IsMinimalIn C S a ∧ IsMaximalIn C S a := by
        intro a ha
        constructor
        · -- a ∈ A₁ is maximal. Show a is also minimal.
          refine ⟨hA₁S ha, fun y hy hya => ?_⟩
          -- y ≤ a. y ∈ S = C+(A₂). So ∃ a₂ ∈ A₂ with a₂ ≤ y.
          have hy_cp : y ∈ cPlus C S A₂ := hcp₂_eq ▸ hy
          simp only [cPlus, Finset.mem_filter] at hy_cp
          obtain ⟨_, a₂, ha₂, ha₂y⟩ := hy_cp
          -- a₂ ≤ y ≤ a. a₂ is minimal → a₂ ≤ y → (if a₂ ∈ S, which it is)
          -- a is maximal → y ≤ a → y = a if y ∈ S? No, maximal means a ≤ z → z = a.
          -- Actually maximal means: y ∈ S, a ≤ y → y = a. Not y ≤ a → y = a.
          -- We need: y ≤ a. To show y = a.
          -- a₂ ≤ y ≤ a. a₂ minimal in S. a maximal in S.
          -- a ∈ S = C+(A₂), so ∃ a₂' ∈ A₂ with a₂' ≤ a.
          have ha_cp : a ∈ cPlus C S A₂ := hcp₂_eq ▸ hA₁S ha
          simp only [cPlus, Finset.mem_filter] at ha_cp
          obtain ⟨_, a₂', ha₂', ha₂'a⟩ := ha_cp
          -- a₂' ≤ a. a₂' is minimal. If a₂' = a, then a is minimal. Done (y ≤ a, a minimal → y = a).
          -- If a₂' ≠ a, a₂' < a strictly. But a₂' is minimal, so no one is below a₂'.
          -- a₂' ∈ A₂, a ∈ A₁. Need to reach contradiction.
          -- Actually: a₂' ≤ a and a₂' is minimal (all A₂ are minimals). a is maximal.
          -- a₂' ∈ S. a₂' ≤ a. a maximal doesn't help (maximal means nothing above a).
          -- a₂' minimal: nothing below a₂'. a₂' ≤ a.
          -- If a₂' ≠ a: a₂' < a. a₂' ∈ A₂, a ∈ A₁.
          -- Now: is a ∈ A₂? Not necessarily.
          -- Consider: a₂' is minimal. b := y satisfies a₂ ≤ y ≤ a and a₂' ≤ a.
          -- Let's try: use a₂' ≤ a to conclude y = a.
          -- We know a₂' ≤ a. (hA₂_min a₂' ha₂').2 says: ∀ z ∈ S, z ≤ a₂' → z = a₂'.
          -- We also know a₂' ≤ a and a is maximal: (hA₁_max a ha).2 says: ∀ z ∈ S, a ≤ z → z = a.
          -- Now: a₂' ≤ y ≤ a. Also a₂' ≤ a. But this doesn't give y = a directly.
          -- KEY IDEA: consider a₂ ∈ A₂ and a ∈ A₁ with a₂ ≤ y ≤ a.
          -- Since a₂ is minimal and a₂ ≤ a (by transitivity a₂ ≤ y ≤ a):
          -- a₂ is minimal, so: for any z ∈ S with z ≤ a₂, z = a₂.
          -- Doesn't directly help.
          -- DIFFERENT APPROACH: since no element is universal (h_no_univ),
          -- for each a ∈ A₁ there's a max antichain missing a.
          -- But A₁ contains all maximals. If a max antichain B misses a (which is maximal),
          -- then B does NOT contain all maximals. B ⊆ S.
          -- B is a max antichain of size w. All elements of B are in S.
          -- a ∉ B. a ∈ A₁. Since A₁ = all maximals, a is maximal.
          -- For each b ∈ B: b ∈ S = C-(A₁), so ∃ a₁ ∈ A₁ with b ≤ a₁.
          -- If b is itself maximal, then b ∈ A₁ (all maximals). But then b ≤ a₁ and b maximal → b = a₁ ∈ A₁.
          -- Since B is antichain of size w = |A₁| and all maximals in B are in A₁...
          -- This is getting circular. Let me try the direct contradiction approach.
          -- Use no_isolated_antichain_covers if we can show all A₁ elements are isolated.
          -- For now, use the fact that a₂' ≤ a and work with a₂' minimal.
          -- If a₂' = a: a is minimal (since a₂' is minimal and a₂' = a). Then y ≤ a and a minimal → y = a.
          exact (hA₂_min a₂' ha₂').2 y hy (C.le_trans y a a₂' hya ha₂'a) ▸
            (C.le_antisymm a₂' a ha₂'a (C.le_trans a₂' y a
              ((hA₂_min a₂' ha₂').2 y hy (C.le_trans y a a₂' hya ha₂'a) ▸ hya)
              (C.le_refl a)) ▸ rfl)
        · exact hA₁_max a ha
      -- Now derive contradiction using no_isolated_antichain_covers
      exact absurd (no_isolated_antichain_covers C S A₁ hA₁S hA₁anti hA₁card h_iso₁ hgt) (not_false)
-/

/-! ### Full chain cover (Dilworth decomposition) -/

/-- **Full Dilworth cover**: S can be covered by ≤ inducedWidth(S) chains,
    each a subset of S.

    Proved by strong induction on |S|:
    - |S| = width: singleton chains (S is antichain).
    - |S| > width, universal element: remove it, IH, add {m}.
    - |S| > width, no universal element: C+/C- merge. -/
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
      -- The proof finds a "good" antichain B with both C+(B) ⊊ S and C-(B) ⊊ S,
      -- applies IH to both, and merges the resulting chain covers at B.
      -- When no single antichain directly gives both proper, we find a comparable
      -- minimal-maximal pair {m, M}, check if removing it decreases width
      -- (chain removal), or else extract a good antichain from S \ {m, M}.
      -- See the detailed proof strategy in the file header comments.
      -- The full formalization of the C+/C- merge is the remaining technical step.
      -- Strategy: find minimal m and maximal M with m < M.
      -- Then either width(S \ {m,M}) < w (chain removal) or
      -- ∃ good antichain B missing both m and M (C+/C- merge at B).
      --
      -- Step 1: S is not an antichain (|S| > w), so ∃ comparable pair.
      -- From comparable pair, extract minimal ≤ maximal.
      have hS_not_anti : ¬ IsAntichain C S := by
        intro hSA
        have : S.card ≤ inducedWidth C S :=
          antichain_card_le_inducedWidth C S S (le_refl S) hSA
        omega
      -- hS_not_anti : ¬ IsAntichain C S
      -- Extract a comparable pair
      have ⟨x₀, hx₀S, y₀, hy₀S, hx₀y₀, hne₀⟩ : ∃ x ∈ S, ∃ y ∈ S, C.le x y ∧ x ≠ y := by
        by_contra h_no_comp
        push_neg at h_no_comp
        exact hS_not_anti (fun a ha b hb hab =>
          ⟨fun hle => hab (h_no_comp a ha b hb hle),
           fun hle => hab (h_no_comp b hb a ha hle).symm⟩)
      -- Get minimal m ≤ x₀ and maximal M ≥ y₀
      obtain ⟨m, hm_min⟩ := exists_minimal C S hS_ne
      obtain ⟨M_top, hM_max⟩ := exists_maximal C S hS_ne
      -- We know x₀ < y₀ (since x₀ ≤ y₀ and x₀ ≠ y₀).
      -- Find a minimal below x₀ and maximal above y₀.
      -- Actually, we just need ANY minimal m and maximal M with m < M.
      -- Since x₀ ≤ y₀ with x₀ ≠ y₀: ∃ minimal m ≤ x₀ ≤ y₀ ≤ maximal M.
      -- We need to find such m and M among the existing minimals/maximals.
      -- Use the filter approach: among elements ≤ x₀, find a minimal.
      -- Among elements ≥ y₀, find a maximal.
      -- Actually, let's just use a simpler approach: find m ≤ x₀ (minimal in {z ∈ S : z ≤ x₀})
      -- and M ≥ y₀ (maximal in {z ∈ S : z ≥ y₀}).
      have hbelow_ne : (S.filter (fun z => C.le z x₀)).Nonempty :=
        ⟨x₀, Finset.mem_filter.mpr ⟨hx₀S, C.le_refl x₀⟩⟩
      obtain ⟨m, hm_min_below⟩ := exists_minimal C (S.filter (fun z => C.le z x₀)) hbelow_ne
      have hmS : m ∈ S := (Finset.mem_filter.mp hm_min_below.1).1
      have hmx₀ : C.le m x₀ := (Finset.mem_filter.mp hm_min_below.1).2
      -- m is minimal in S (not just in the filter)
      have hm_min_S : IsMinimalIn C S m := by
        refine ⟨hmS, fun z hz hzm => ?_⟩
        -- z ≤ m ≤ x₀, so z is in the filter
        have hzx₀ : C.le z x₀ := C.le_trans z m x₀ hzm hmx₀
        have hz_filt : z ∈ S.filter (fun z => C.le z x₀) := Finset.mem_filter.mpr ⟨hz, hzx₀⟩
        exact hm_min_below.2 z hz_filt hzm
      have habove_ne : (S.filter (fun z => C.le y₀ z)).Nonempty :=
        ⟨y₀, Finset.mem_filter.mpr ⟨hy₀S, C.le_refl y₀⟩⟩
      obtain ⟨M, hM_max_above⟩ := exists_maximal C (S.filter (fun z => C.le y₀ z)) habove_ne
      have hMS : M ∈ S := (Finset.mem_filter.mp hM_max_above.1).1
      have hy₀M : C.le y₀ M := (Finset.mem_filter.mp hM_max_above.1).2
      have hM_max_S : IsMaximalIn C S M := by
        refine ⟨hMS, fun z hz hMz => ?_⟩
        have hy₀z : C.le y₀ z := C.le_trans y₀ M z hy₀M hMz
        have hz_filt : z ∈ S.filter (fun z => C.le y₀ z) := Finset.mem_filter.mpr ⟨hz, hy₀z⟩
        exact hM_max_above.2 z hz_filt hMz
      -- m ≤ x₀ ≤ y₀ ≤ M
      have hmM : C.le m M := C.le_trans m x₀ M hmx₀ (C.le_trans x₀ y₀ M hx₀y₀ hy₀M)
      have hmne : m ≠ M := by
        intro heq; subst heq
        -- m = M means m ≤ x₀ ≤ y₀ ≤ m, so x₀ = y₀ = m
        have := C.le_antisymm x₀ m (C.le_trans x₀ y₀ m hx₀y₀ hy₀M) hmx₀
        have := C.le_antisymm y₀ m hy₀M (C.le_trans m x₀ y₀ hmx₀ hx₀y₀)
        -- x₀ = m and y₀ = m, so x₀ = y₀, contradicting hne₀
        have hx₀m : x₀ = m := C.le_antisymm x₀ m (C.le_trans x₀ y₀ m hx₀y₀ hy₀M) hmx₀
        have hy₀m : y₀ = m := C.le_antisymm y₀ m hy₀M (C.le_trans m x₀ y₀ hmx₀ hx₀y₀)
        exact hne₀ (hx₀m.trans hy₀m.symm)
      -- Step 2: Either width(S \ {m, M}) < w or find good antichain
      set pair := ({m, M} : Finset C.Λ) with hpair_def
      have hpair_sub : pair ⊆ S := by
        intro z hz
        simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hpair_chain : IsChainFS C pair := by
        intro a ha b hb
        simp only [pair, Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl
        · rcases hb with rfl | rfl
          · left; exact C.le_refl _
          · left; exact hmM
        · rcases hb with rfl | rfl
          · right; exact hmM
          · left; exact C.le_refl _
      -- Check width of S \ pair
      by_cases h_wd : inducedWidth C (S \ pair) < inducedWidth C S
      · -- Width decreases: chain removal. IH on S \ pair.
        have hpair_card : (S \ pair).card ≤ n := by
          have : (S \ pair).card < S.card := by
            apply Finset.card_lt_card
            exact ⟨Finset.sdiff_subset, fun h =>
              (Finset.mem_sdiff.mp (h hmS)).2
                (Finset.mem_insert.mpr (Or.inl rfl))⟩
          omega
        obtain ⟨chains', hch', hcov', hcard'⟩ := ih (S \ pair) hpair_card
        refine ⟨insert pair chains', ?_, ?_, ?_⟩
        · intro L hL
          rw [Finset.mem_insert] at hL
          rcases hL with rfl | hL
          · exact ⟨hpair_sub, hpair_chain⟩
          · obtain ⟨hLS, hLchain⟩ := hch' L hL
            exact ⟨Finset.Subset.trans hLS Finset.sdiff_subset, hLchain⟩
        · intro x hx
          by_cases hx_pair : x ∈ pair
          · exact ⟨pair, Finset.mem_insert_self _ _, hx_pair⟩
          · obtain ⟨L, hL, hxL⟩ := hcov' x (Finset.mem_sdiff.mpr ⟨hx, hx_pair⟩)
            exact ⟨L, Finset.mem_insert.mpr (Or.inr hL), hxL⟩
        · calc (insert pair chains').card
              ≤ chains'.card + 1 := Finset.card_insert_le _ _
            _ ≤ inducedWidth C (S \ pair) + 1 := by omega
            _ ≤ inducedWidth C S := by omega
      · -- Width doesn't decrease: ∃ antichain B of size w in S \ pair.
        -- B misses m (minimal) and M (maximal), so both C+(B) and C-(B) are proper.
        push_neg at h_wd
        -- width(S \ pair) ≥ w. Also ≤ w (monotonicity). So = w.
        have h_wd_eq : inducedWidth C (S \ pair) = inducedWidth C S := by
          apply le_antisymm
          · exact inducedWidth_mono C _ _ Finset.sdiff_subset
          · exact h_wd
        -- Get max antichain B in S \ pair
        have hSp_ne : (S \ pair).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          have := inducedWidth_empty C (k := k)
          rw [← h] at this; omega
        obtain ⟨B, hBS', hBanti, hBcard⟩ := exists_max_antichain C (S \ pair) (by omega)
        rw [h_wd_eq] at hBcard
        have hBS : B ⊆ S := Finset.Subset.trans hBS' Finset.sdiff_subset
        -- m ∉ B and M ∉ B (since B ⊆ S \ pair)
        have hm_notB : m ∉ B := fun hm => by
          have := hBS' hm
          rw [Finset.mem_sdiff] at this
          exact this.2 (Finset.mem_insert.mpr (Or.inl rfl))
        have hM_notB : M ∉ B := fun hM_mem => by
          have := hBS' hM_mem
          rw [Finset.mem_sdiff] at this
          exact this.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
        -- B is a good antichain: C+(B) ⊊ S and C-(B) ⊊ S
        have hcp : cPlus C S B ⊂ S :=
          cPlus_ssubset C S B hBS hBanti hBcard m hm_min_S hm_notB
        have hcm : cMinus C S B ⊂ S :=
          cMinus_ssubset C S B hBS hBanti hBcard M hM_max_S hM_notB
        -- C+/C- merge at B.
        -- IH on C+(B) and C-(B)
        have hwp := width_cPlus_eq C S B hBS hBanti hBcard
        have hwm := width_cMinus_eq C S B hBS hBanti hBcard
        have hcp_card : (cPlus C S B).card ≤ n := by
          have : (cPlus C S B).card < S.card := Finset.card_lt_card hcp; omega
        have hcm_card : (cMinus C S B).card ≤ n := by
          have : (cMinus C S B).card < S.card := Finset.card_lt_card hcm; omega
        obtain ⟨chains_p, hch_p, hcov_p, hcard_p⟩ := ih (cPlus C S B) hcp_card
        obtain ⟨chains_m, hch_m, hcov_m, hcard_m⟩ := ih (cMinus C S B) hcm_card
        rw [hwp] at hcard_p; rw [hwm] at hcard_m
        have hcard_p_B : chains_p.card ≤ B.card := hBcard ▸ hcard_p
        have hcard_m_B : chains_m.card ≤ B.card := hBcard ▸ hcard_m
        -- For each a ∈ B, get the C+ chain and C- chain containing a
        have hB_sub_cp : B ⊆ cPlus C S B := antichain_subset_cPlus C S B hBS
        have hB_sub_cm : B ⊆ cMinus C S B := antichain_subset_cMinus C S B hBS
        -- Build the merged cover using a function B → Finset C.Λ
        -- For each a ∈ B, choose the C+ chain Lp(a) and C- chain Lm(a) containing a,
        -- then form Lp(a) ∪ Lm(a).
        -- Use the suffices trick: show ∃ function giving chains indexed by B.
        suffices h_merge : ∃ (f : C.Λ → Finset C.Λ),
            (∀ a ∈ B, f a ⊆ S ∧ IsChainFS C (f a)) ∧
            (∀ x ∈ S, ∃ a ∈ B, x ∈ f a) by
          obtain ⟨f, hf_ch, hf_cov⟩ := h_merge
          exact ⟨B.image f,
            fun L hL => by
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hL; exact hf_ch a ha,
            fun x hx => by
              obtain ⟨a, ha, hxa⟩ := hf_cov x hx
              exact ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hxa⟩,
            le_trans Finset.card_image_le (hBcard ▸ le_refl _)⟩
        -- Construct f using Classical.choose
        -- For each a ∈ C+(B), choose a chain in chains_p containing a.
        -- For each a ∈ C-(B), choose a chain in chains_m containing a.
        -- f(a) = chosen_p(a) ∪ chosen_m(a)
        -- First, build the choice functions (defined for all a, but only meaningful for a ∈ B)
        have h_pick_p : ∀ a ∈ B, ∃ L ∈ chains_p, a ∈ L :=
          fun a ha => hcov_p a (hB_sub_cp ha)
        have h_pick_m : ∀ a ∈ B, ∃ L ∈ chains_m, a ∈ L :=
          fun a ha => hcov_m a (hB_sub_cm ha)
        -- Use Classical.choose to pick chains
        -- We need to handle the dependent types carefully
        refine ⟨fun a =>
          if ha : a ∈ B then
            Classical.choose (h_pick_p a ha) ∪ Classical.choose (h_pick_m a ha)
          else ∅, ?_, ?_⟩
        · -- Each f(a) is a subset of S and a chain
          intro a haB
          simp only [dif_pos haB]
          set Lp := Classical.choose (h_pick_p a haB)
          set Lm := Classical.choose (h_pick_m a haB)
          have hLp_spec := Classical.choose_spec (h_pick_p a haB)
          have hLm_spec := Classical.choose_spec (h_pick_m a haB)
          obtain ⟨hLp_mem, haLp⟩ := hLp_spec
          obtain ⟨hLm_mem, haLm⟩ := hLm_spec
          constructor
          · -- Lp ∪ Lm ⊆ S
            intro x hx
            rw [Finset.mem_union] at hx
            rcases hx with hx | hx
            · exact cPlus_subset C S B ((hch_p Lp hLp_mem).1 hx)
            · exact cMinus_subset C S B ((hch_m Lm hLm_mem).1 hx)
          · -- Lp ∪ Lm is a chain
            -- Elements of Lm are ≤ a (by cMinus_chain_all_le_rep)
            -- Elements of Lp are ≥ a (by cPlus_chain_all_ge_rep)
            -- So merge_is_chain applies
            have hbij_p := chain_cover_antichain_bijection C B (cPlus C S B) hB_sub_cp
              hBanti chains_p (fun L hL => (hch_p L hL).2) hcov_p hcard_p_B
            have hbij_m := chain_cover_antichain_bijection C B (cMinus C S B) hB_sub_cm
              hBanti chains_m (fun L hL => (hch_m L hL).2) hcov_m hcard_m_B
            obtain ⟨_, _, h_uniq_p⟩ := hbij_p Lp hLp_mem
            obtain ⟨_, _, h_uniq_m⟩ := hbij_m Lm hLm_mem
            have h_a_uniq_p : ∀ b, b ∈ B ∧ b ∈ Lp → b = a := by
              intro b hb
              have hb_eq := h_uniq_p b hb
              have ha_eq := h_uniq_p a ⟨haB, haLp⟩
              exact hb_eq.trans ha_eq.symm
            have h_a_uniq_m : ∀ b, b ∈ B ∧ b ∈ Lm → b = a := by
              intro b hb
              have hb_eq := h_uniq_m b hb
              have ha_eq := h_uniq_m a ⟨haB, haLm⟩
              exact hb_eq.trans ha_eq.symm
            have h_le_a : ∀ x ∈ Lm, C.le x a :=
              cMinus_chain_all_le_rep C S B Lm a hBanti hBS
                (hch_m Lm hLm_mem).2 (fun x hx => (hch_m Lm hLm_mem).1 hx)
                haLm haB h_a_uniq_m
            have h_ge_a : ∀ x ∈ Lp, C.le a x :=
              cPlus_chain_all_ge_rep C S B Lp a hBanti hBS
                (hch_p Lp hLp_mem).2 (fun x hx => (hch_p Lp hLp_mem).1 hx)
                haLp haB h_a_uniq_p
            rw [Finset.union_comm]
            exact merge_is_chain C Lm Lp a (hch_m Lm hLm_mem).2 (hch_p Lp hLp_mem).2
              h_le_a h_ge_a
        · -- f covers S
          intro x hx
          -- x ∈ S = C+(B) ∪ C-(B)
          have hx_union := (cPlus_union_cMinus C S B hBS hBanti hBcard).symm ▸ hx
          rw [Finset.mem_union] at hx_union
          rcases hx_union with hx_cp | hx_cm
          · -- x ∈ C+(B): x is in some chain of chains_p
            obtain ⟨L, hL, hxL⟩ := hcov_p x hx_cp
            -- L has a unique B-element a₀
            have hbij_p := chain_cover_antichain_bijection C B (cPlus C S B) hB_sub_cp
              hBanti chains_p (fun L' hL' => (hch_p L' hL').2) hcov_p hcard_p_B
            obtain ⟨a₀, ⟨ha₀B, ha₀L⟩, _⟩ := hbij_p L hL
            -- x is in f(a₀) = Lp(a₀) ∪ Lm(a₀)
            refine ⟨a₀, ha₀B, ?_⟩
            simp only [dif_pos ha₀B]
            rw [Finset.mem_union]
            left
            -- Need: x ∈ Classical.choose (h_pick_p a₀ ha₀B)
            -- Classical.choose gives SOME chain containing a₀.
            -- But x is in L which also contains a₀.
            -- We need x to be in the CHOSEN chain, not just in L.
            -- This is the chain-uniqueness issue!
            -- If a₀ is in only one chain of chains_p, then the chosen chain = L.
            -- But a₀ could be in multiple chains (the cover allows overlaps).
            -- However, by the bijection counting argument, a₀ is in exactly one chain.
            -- We need to prove this.
            -- Actually, the bijection says each chain has a UNIQUE B-element.
            -- But it doesn't directly say each B-element is in a UNIQUE chain.
            -- The counting argument: |chains_p| ≤ w = |B|, each chain has exactly 1 B-elem,
            -- each B-elem is in ≥ 1 chain. So the map chain → B-elem is surjective onto B
            -- (|chains_p| = |B| forced by counting). And injective (each chain gives different B-elem).
            -- So it's a bijection. The inverse: each B-elem → unique chain.
            -- But this injectivity argument is exactly what chain_unique_of_bijection was supposed to prove.
            -- Let me prove it inline.
            -- Actually: from hbij_p, each chain L has ∃! a, a ∈ B ∧ a ∈ L.
            -- From the sum argument in chain_cover_antichain_bijection:
            -- ∑ |B ∩ L| = |B| and each |B ∩ L| = 1 and |chains_p| = |B|.
            -- If a₀ ∈ L and a₀ ∈ L', both in chains_p, with L ≠ L':
            -- |B ∩ L| = 1 (containing a₀) and |B ∩ L'| ≥ 1 (containing a₀).
            -- But L's unique B-elem is a₀ and L''s unique B-elem is also a₀.
            -- Wait, L' could have unique B-elem ≠ a₀ but also contain a₀ (with a₀ ∈ L' but not the "unique" one).
            -- No! Unique means: ∃! b, b ∈ B ∧ b ∈ L'. So if a₀ ∈ B ∧ a₀ ∈ L': the unique b = a₀.
            -- Similarly for L: unique b = a₀.
            -- Now: other B-elements a₁ ≠ a₀ must be in some chain. Not in L (unique is a₀, so a₁ ∉ L or a₁ ∉ B... a₁ ∈ B but if a₁ ∈ L then a₁ ∈ B ∧ a₁ ∈ L, and unique gives a₁ = a₀, contradiction).
            -- So a₁ ∉ L for all a₁ ∈ B \ {a₀}. Similarly a₁ ∉ L'.
            -- So a₁ is in some chain L'' ∉ {L, L'}.
            -- |B \ {a₀}| = w - 1 elements need chains from chains_p \ {L, L'}.
            -- |chains_p \ {L, L'}| ≤ w - 2 (since L ≠ L').
            -- Each remaining chain has 1 B-elem. So w - 1 ≤ w - 2. Contradiction!
            -- This proves L = L'. So a₀ is in exactly one chain.
            -- Now: Classical.choose picks that unique chain, which is L.
            -- Let me prove this step.
            have hLp_chosen := Classical.choose_spec (h_pick_p a₀ ha₀B)
            set Lp_chosen := Classical.choose (h_pick_p a₀ ha₀B) with hLp_def
            obtain ⟨hLp_ch_mem, ha₀_Lp_ch⟩ := hLp_chosen
            -- Show Lp_chosen = L (both contain a₀, and a₀ is in exactly one chain)
            suffices hL_eq : Lp_chosen = L by rw [hL_eq]; exact hxL
            -- Both have unique B-element a₀
            obtain ⟨b_ch, ⟨hb_chB, hb_ch_mem⟩, hb_ch_uniq⟩ := hbij_p Lp_chosen hLp_ch_mem
            obtain ⟨b_L, ⟨hb_LB, hb_L_mem⟩, hb_L_uniq⟩ := hbij_p L hL
            -- a₀ ∈ B ∧ a₀ ∈ Lp_chosen → a₀ = b_ch
            have : a₀ = b_ch := hb_ch_uniq a₀ ⟨ha₀B, ha₀_Lp_ch⟩
            -- a₀ ∈ B ∧ a₀ ∈ L → a₀ = b_L
            have : a₀ = b_L := hb_L_uniq a₀ ⟨ha₀B, ha₀L⟩
            -- Suppose Lp_chosen ≠ L. Derive contradiction.
            by_contra hneq
            -- a₀ is in both Lp_chosen and L (different chains).
            -- Other B-elements can't be in Lp_chosen or L (uniqueness).
            -- Count: (B \ {a₀}).card = w - 1 elements need chains from chains_p \ {Lp_chosen, L}.
            -- |chains_p \ {Lp_chosen, L}| ≤ |chains_p| - 2.
            -- Each chain has 1 B-elem. So w - 1 ≤ |chains_p| - 2 ≤ w - 2. Contradiction.
            have h_other_not_in : ∀ a' ∈ B, a' ≠ a₀ → a' ∉ Lp_chosen ∧ a' ∉ L := by
              intro a' ha'B ha'ne
              constructor
              · intro ha'_ch
                exact ha'ne ((hb_ch_uniq a' ⟨ha'B, ha'_ch⟩).trans (hb_ch_uniq a₀ ⟨ha₀B, ha₀_Lp_ch⟩).symm)
              · intro ha'_L
                exact ha'ne ((hb_L_uniq a' ⟨ha'B, ha'_L⟩).trans (hb_L_uniq a₀ ⟨ha₀B, ha₀L⟩).symm)
            -- Each a' ∈ B \ {a₀} is in some chain L' ∈ chains_p \ {Lp_chosen, L}
            have h_other_covered : ∀ a' ∈ B, a' ≠ a₀ →
                ∃ L' ∈ chains_p, L' ≠ Lp_chosen ∧ L' ≠ L ∧ a' ∈ L' := by
              intro a' ha'B ha'ne
              obtain ⟨L', hL', ha'L'⟩ := hcov_p a' (hB_sub_cp ha'B)
              have h_not := h_other_not_in a' ha'B ha'ne
              exact ⟨L', hL', fun heq => h_not.1 (heq ▸ ha'L'), fun heq => h_not.2 (heq ▸ ha'L'), ha'L'⟩
            -- The chains used by B \ {a₀} are in chains_p \ {Lp_chosen, L}
            -- Each such chain has exactly 1 B-element, so they're all distinct.
            -- |B \ {a₀}| distinct chains from chains_p \ {Lp_chosen, L}
            -- |B \ {a₀}| = |B| - 1 = w - 1
            -- |chains_p \ {Lp_chosen, L}| ≤ |chains_p| - 2
            -- w - 1 ≤ w - 2: contradiction
            -- Actually proving this counting bound formally requires some work.
            -- Let me use a simpler approach.
            -- ∑_{L ∈ chains_p} |B.filter (· ∈ L)| ≥ |B| (each b ∈ B is in some chain)
            -- Each term ≤ 1 (chain ∩ antichain). So ∑ = |B| = |chains_p| (forced).
            -- Lp_chosen and L both have |B ∩ ·| = 1 (containing a₀).
            -- Remaining chains: ∑ = |B| - 2 (at most, since a₀ counted twice).
            -- Wait, the sum counts a₀ once per chain containing it.
            -- ∑ |B ∩ L| ≥ 1 (Lp_chosen) + 1 (L) + |B \ {a₀}| (each other b in some chain)
            -- = 2 + (|B| - 1) = |B| + 1
            -- But ∑ ≤ |chains_p| ≤ |B|. Contradiction.
            -- Let me formalize this counting argument directly.
            -- Actually, card_biUnion_le gives ∑ ≥ |biUnion|.
            -- And we know |biUnion| ≥ |B|. And ∑ ≤ |chains_p|.
            -- With the extra chain, ∑ ≥ |B| + 1.
            -- Use: Finset.add_sum_erase for Lp_chosen:
            -- |B ∩ Lp_chosen| + ∑_{L' ≠ Lp_chosen} |B ∩ L'| = ∑
            -- |B ∩ Lp_chosen| = 1. ∑_{L' ≠ Lp_chosen} |B ∩ L'| = ∑ - 1.
            -- Among L' ≠ Lp_chosen: L is one of them. |B ∩ L| ≥ 1 (a₀ ∈ B ∩ L).
            -- So ∑_{L' ≠ Lp_chosen} ≥ 1 + (contributions from B \ {a₀}).
            -- B \ {a₀}: each element is in some chain L' ≠ Lp_chosen (and ≠ L by uniqueness).
            -- So ∑_{L' ≠ Lp_chosen, L' ≠ L} ≥ |B \ {a₀}| = |B| - 1.
            -- Total: 1 + 1 + (|B| - 1) = |B| + 1 > |chains_p| ≥ |B|. Wait: ∑ ≤ |chains_p| ≤ |B|.
            -- But ∑ = ∑_{terms} where each ≤ 1. ∑ ≤ |chains_p|.
            -- Hmm: ∑ = |chains_p| (exact) since each term is 1 and there are |chains_p| terms.
            -- Wait no: each term is ≤ 1 but could be 0. ∑ ≤ |chains_p|.
            -- And ∑ ≥ |B| (from coverage). So ∑ ∈ [|B|, |chains_p|].
            -- Since |chains_p| ≤ |B|: ∑ = |B| = |chains_p|.
            -- So each term = 1 (no chain has 0 B-elements).
            -- Lp_chosen: 1 B-element (a₀). L: 1 B-element (a₀).
            -- Other chains: 1 B-element each, all ≠ a₀.
            -- So a₀ is the only B-element in Lp_chosen, a₀ is the only B-element in L.
            -- Other |chains_p| - 2 chains have |B| - 2 ... wait, we need |B| elements covered.
            -- a₀ is covered by Lp_chosen (and L). Other |B| - 1 elements need other chains.
            -- Other chains: |chains_p| - 2 (removing Lp_chosen and L).
            -- Each has exactly 1 B-element. So |B| - 1 ≤ |chains_p| - 2 ≤ |B| - 2.
            -- |B| - 1 ≤ |B| - 2: contradiction (|B| = w ≥ 1).
            -- OK this is correct but formalizing all this is very tedious.
            -- Let me use omega or a direct calculation.
            -- For expediency, I'll use a Finset.sum argument.
            have h_le_one : ∀ L' ∈ chains_p, (B.filter (fun b => b ∈ L')).card ≤ 1 := by
              intro L' hL'
              have hBL_eq : B.filter (fun b => b ∈ L') = B ∩ L' := by
                ext x; simp [Finset.mem_filter, Finset.mem_inter]
              rw [hBL_eq, Finset.inter_comm]
              exact chain_antichain_inter_card_le_one C L' B (hch_p L' hL').2 hBanti
            have h_sum_ge : B.card ≤ chains_p.sum (fun L' => (B.filter (fun b => b ∈ L')).card) := by
              calc B.card
                  ≤ (chains_p.biUnion (fun L' => B.filter (fun b => b ∈ L'))).card := by
                    apply Finset.card_le_card
                    intro b hb; rw [Finset.mem_biUnion]
                    obtain ⟨L', hL', hbL'⟩ := hcov_p b (hB_sub_cp hb)
                    exact ⟨L', hL', Finset.mem_filter.mpr ⟨hb, hbL'⟩⟩
                _ ≤ chains_p.sum (fun L' => (B.filter (fun b => b ∈ L')).card) :=
                    Finset.card_biUnion_le
            have h_sum_le : chains_p.sum (fun L' => (B.filter (fun b => b ∈ L')).card) ≤ chains_p.card :=
              le_trans (Finset.sum_le_sum h_le_one) (by simp)
            -- a₀ ∈ B ∩ Lp_chosen, so |B ∩ Lp_chosen| ≥ 1
            have h_ch_ge : (B.filter (fun b => b ∈ Lp_chosen)).card ≥ 1 := by
              exact Finset.card_pos.mpr ⟨a₀, Finset.mem_filter.mpr ⟨ha₀B, ha₀_Lp_ch⟩⟩
            -- a₀ ∈ B ∩ L, so |B ∩ L| ≥ 1
            have h_L_ge : (B.filter (fun b => b ∈ L)).card ≥ 1 := by
              exact Finset.card_pos.mpr ⟨a₀, Finset.mem_filter.mpr ⟨ha₀B, ha₀L⟩⟩
            -- The counting contradiction: each chain has ≤ 1 B-elem, |chains_p| ≤ |B|,
            -- but a₀ is in both Lp_chosen and L (distinct chains), so |B| - 1 other elements
            -- need |chains_p| - 2 chains, giving |B| - 1 ≤ |B| - 2. Contradiction.
            have hL_in_erase : L ∈ chains_p.erase Lp_chosen :=
              Finset.mem_erase.mpr ⟨Ne.symm hneq, hL⟩
            -- Injection: each a' ∈ B \ {a₀} maps to a distinct chain in chains_p \ {Lp_chosen, L}
            have h_inj : ∀ a' ∈ B.erase a₀, ∃ L' ∈ (chains_p.erase Lp_chosen).erase L, a' ∈ L' := by
              intro a' ha'
              rw [Finset.mem_erase] at ha'
              obtain ⟨L', hL', ha'L'⟩ := hcov_p a' (hB_sub_cp ha'.2)
              have ha'ne := ha'.1
              have hL'_ne_ch : L' ≠ Lp_chosen := by
                intro heq; subst heq
                exact ha'ne ((hb_ch_uniq a' ⟨ha'.2, ha'L'⟩).trans (hb_ch_uniq a₀ ⟨ha₀B, ha₀_Lp_ch⟩).symm)
              have hL'_ne_L : L' ≠ L := by
                intro heq; subst heq
                exact ha'ne ((hb_L_uniq a' ⟨ha'.2, ha'L'⟩).trans (hb_L_uniq a₀ ⟨ha₀B, ha₀L⟩).symm)
              exact ⟨L', Finset.mem_erase.mpr ⟨hL'_ne_L, Finset.mem_erase.mpr ⟨hL'_ne_ch, hL'⟩⟩, ha'L'⟩
            -- Each a' lands in a chain with ≤ 1 B-element, so distinct a' give distinct chains
            -- Count: |B \ {a₀}| = |B| - 1
            -- |chains_p \ {Lp_chosen, L}| ≤ |chains_p| - 2 (since Lp_chosen ≠ L are both in chains_p)
            -- We need |B| - 1 ≤ |chains_p| - 2 and |chains_p| ≤ |B|, giving |B| - 1 ≤ |B| - 2
            -- Use that (B.erase a₀).card ≤ ((chains_p.erase Lp_chosen).erase L).card
            -- by injecting each a' into a distinct chain (each chain has ≤ 1 B-elem, all in antichain,
            -- and different a' can't be in the same chain since it would have 2 B-elements)
            -- Build a function B.erase a₀ → (chains_p.erase Lp_chosen).erase L
            -- Actually, easier: use the sum argument more directly
            have h_remaining_ge : ((chains_p.erase Lp_chosen).erase L).card ≥ B.card - 1 := by
              have h_card_bound : (B.erase a₀).card ≤ ((chains_p.erase Lp_chosen).erase L).card := by
                calc (B.erase a₀).card
                    ≤ (((chains_p.erase Lp_chosen).erase L).biUnion
                        (fun L' => B.filter (fun b => b ∈ L'))).card := by
                      apply Finset.card_le_card
                      intro b hb
                      rw [Finset.mem_erase] at hb
                      rw [Finset.mem_biUnion]
                      obtain ⟨L', hL', hbL'⟩ := h_inj b (Finset.mem_erase.mpr hb)
                      exact ⟨L', hL', Finset.mem_filter.mpr ⟨hb.2, hbL'⟩⟩
                  _ ≤ ((chains_p.erase Lp_chosen).erase L).sum
                        (fun L' => (B.filter (fun b => b ∈ L')).card) :=
                      Finset.card_biUnion_le
                  _ ≤ ((chains_p.erase Lp_chosen).erase L).sum (fun _ => 1) := by
                      apply Finset.sum_le_sum
                      intro L' hL'
                      have hL'_mem : L' ∈ chains_p := by
                        exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hL')
                      have hBL_eq : B.filter (fun b => b ∈ L') = B ∩ L' := by
                        ext x; simp [Finset.mem_filter, Finset.mem_inter]
                      rw [hBL_eq, Finset.inter_comm]
                      exact chain_antichain_inter_card_le_one C L' B (hch_p L' hL'_mem).2 hBanti
                  _ = ((chains_p.erase Lp_chosen).erase L).card := by simp
              rw [Finset.card_erase_of_mem ha₀B] at h_card_bound
              exact h_card_bound
            -- Now: chains_p has Lp_chosen and L as distinct elements
            have h_two_le : 2 ≤ chains_p.card := by
              calc 2 = ({Lp_chosen, L} : Finset _).card := by
                    rw [Finset.card_pair hneq]
                _ ≤ chains_p.card := Finset.card_le_card (by
                    intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact hLp_ch_mem
                    · exact hL)
            have h_erase_card : ((chains_p.erase Lp_chosen).erase L).card = chains_p.card - 2 := by
              rw [Finset.card_erase_of_mem hL_in_erase, Finset.card_erase_of_mem hLp_ch_mem]; omega
            have hB_pos : B.card ≥ 1 := hBcard ▸ hS_w
            have hcp_le_B : chains_p.card ≤ B.card := hcard_p_B
            omega
          · -- x ∈ C-(B): similar argument
            obtain ⟨L, hL, hxL⟩ := hcov_m x hx_cm
            have hbij_m := chain_cover_antichain_bijection C B (cMinus C S B) hB_sub_cm
              hBanti chains_m (fun L' hL' => (hch_m L' hL').2) hcov_m hcard_m_B
            obtain ⟨a₀, ⟨ha₀B, ha₀L⟩, _⟩ := hbij_m L hL
            refine ⟨a₀, ha₀B, ?_⟩
            simp only [dif_pos ha₀B]
            rw [Finset.mem_union]; right
            -- Same uniqueness argument for chains_m
            have hLm_chosen := Classical.choose_spec (h_pick_m a₀ ha₀B)
            set Lm_chosen := Classical.choose (h_pick_m a₀ ha₀B) with hLm_def
            obtain ⟨hLm_ch_mem, ha₀_Lm_ch⟩ := hLm_chosen
            suffices hL_eq : Lm_chosen = L by rw [hL_eq]; exact hxL
            obtain ⟨b_ch, ⟨hb_chB, hb_ch_mem⟩, hb_ch_uniq⟩ := hbij_m Lm_chosen hLm_ch_mem
            obtain ⟨b_L, ⟨hb_LB, hb_L_mem⟩, hb_L_uniq⟩ := hbij_m L hL
            by_contra hneq
            have h_other_not_in : ∀ a' ∈ B, a' ≠ a₀ → a' ∉ Lm_chosen ∧ a' ∉ L := by
              intro a' ha'B ha'ne
              constructor
              · intro ha'_ch
                exact ha'ne ((hb_ch_uniq a' ⟨ha'B, ha'_ch⟩).trans (hb_ch_uniq a₀ ⟨ha₀B, ha₀_Lm_ch⟩).symm)
              · intro ha'_L
                exact ha'ne ((hb_L_uniq a' ⟨ha'B, ha'_L⟩).trans (hb_L_uniq a₀ ⟨ha₀B, ha₀L⟩).symm)
            have h_le_one : ∀ L' ∈ chains_m, (B.filter (fun b => b ∈ L')).card ≤ 1 := by
              intro L' hL'
              have hBL_eq : B.filter (fun b => b ∈ L') = B ∩ L' := by
                ext x'; simp [Finset.mem_filter, Finset.mem_inter]
              rw [hBL_eq, Finset.inter_comm]
              exact chain_antichain_inter_card_le_one C L' B (hch_m L' hL').2 hBanti
            have h_sum_ge : B.card ≤ chains_m.sum (fun L' => (B.filter (fun b => b ∈ L')).card) := by
              calc B.card
                  ≤ (chains_m.biUnion (fun L' => B.filter (fun b => b ∈ L'))).card := by
                    apply Finset.card_le_card
                    intro b hb; rw [Finset.mem_biUnion]
                    obtain ⟨L', hL', hbL'⟩ := hcov_m b (hB_sub_cm hb)
                    exact ⟨L', hL', Finset.mem_filter.mpr ⟨hb, hbL'⟩⟩
                _ ≤ _ := Finset.card_biUnion_le
            have h_sum_le : chains_m.sum (fun L' => (B.filter (fun b => b ∈ L')).card) ≤ chains_m.card :=
              le_trans (Finset.sum_le_sum h_le_one) (by simp)
            have h_ch_ge : (B.filter (fun b => b ∈ Lm_chosen)).card ≥ 1 := by
              exact Finset.card_pos.mpr ⟨a₀, Finset.mem_filter.mpr ⟨ha₀B, ha₀_Lm_ch⟩⟩
            have h_L_ge : (B.filter (fun b => b ∈ L)).card ≥ 1 := by
              exact Finset.card_pos.mpr ⟨a₀, Finset.mem_filter.mpr ⟨ha₀B, ha₀L⟩⟩
            have hLm_in_erase : L ∈ chains_m.erase Lm_chosen :=
              Finset.mem_erase.mpr ⟨Ne.symm hneq, hL⟩
            -- Injection: each a' ∈ B \ {a₀} maps to a chain in chains_m \ {Lm_chosen, L}
            have h_inj_m : ∀ a' ∈ B.erase a₀, ∃ L' ∈ (chains_m.erase Lm_chosen).erase L, a' ∈ L' := by
              intro a' ha'
              rw [Finset.mem_erase] at ha'
              obtain ⟨L', hL', ha'L'⟩ := hcov_m a' (hB_sub_cm ha'.2)
              have ha'ne := ha'.1
              have hL'_ne_ch : L' ≠ Lm_chosen := by
                intro heq; subst heq
                exact ha'ne ((hb_ch_uniq a' ⟨ha'.2, ha'L'⟩).trans (hb_ch_uniq a₀ ⟨ha₀B, ha₀_Lm_ch⟩).symm)
              have hL'_ne_L : L' ≠ L := by
                intro heq; subst heq
                exact ha'ne ((hb_L_uniq a' ⟨ha'.2, ha'L'⟩).trans (hb_L_uniq a₀ ⟨ha₀B, ha₀L⟩).symm)
              exact ⟨L', Finset.mem_erase.mpr ⟨hL'_ne_L, Finset.mem_erase.mpr ⟨hL'_ne_ch, hL'⟩⟩, ha'L'⟩
            have h_remaining_ge : ((chains_m.erase Lm_chosen).erase L).card ≥ B.card - 1 := by
              have h_card_bound : (B.erase a₀).card ≤ ((chains_m.erase Lm_chosen).erase L).card := by
                calc (B.erase a₀).card
                    ≤ (((chains_m.erase Lm_chosen).erase L).biUnion
                        (fun L' => B.filter (fun b => b ∈ L'))).card := by
                      apply Finset.card_le_card
                      intro b hb
                      rw [Finset.mem_erase] at hb
                      rw [Finset.mem_biUnion]
                      obtain ⟨L', hL', hbL'⟩ := h_inj_m b (Finset.mem_erase.mpr hb)
                      exact ⟨L', hL', Finset.mem_filter.mpr ⟨hb.2, hbL'⟩⟩
                  _ ≤ ((chains_m.erase Lm_chosen).erase L).sum
                        (fun L' => (B.filter (fun b => b ∈ L')).card) :=
                      Finset.card_biUnion_le
                  _ ≤ ((chains_m.erase Lm_chosen).erase L).sum (fun _ => 1) := by
                      apply Finset.sum_le_sum
                      intro L' hL'
                      have hL'_mem : L' ∈ chains_m := by
                        exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hL')
                      have hBL_eq : B.filter (fun b => b ∈ L') = B ∩ L' := by
                        ext x'; simp [Finset.mem_filter, Finset.mem_inter]
                      rw [hBL_eq, Finset.inter_comm]
                      exact chain_antichain_inter_card_le_one C L' B (hch_m L' hL'_mem).2 hBanti
                  _ = ((chains_m.erase Lm_chosen).erase L).card := by simp
              rw [Finset.card_erase_of_mem ha₀B] at h_card_bound
              exact h_card_bound
            have h_two_le : 2 ≤ chains_m.card := by
              calc 2 = ({Lm_chosen, L} : Finset _).card := by
                    rw [Finset.card_pair hneq]
                _ ≤ chains_m.card := Finset.card_le_card (by
                    intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl
                    · exact hLm_ch_mem
                    · exact hL)
            have h_erase_card : ((chains_m.erase Lm_chosen).erase L).card = chains_m.card - 2 := by
              rw [Finset.card_erase_of_mem hLm_in_erase, Finset.card_erase_of_mem hLm_ch_mem]; omega
            have hcm_le_B : chains_m.card ≤ B.card := hcard_m_B
            have hB_pos : B.card ≥ 1 := hBcard ▸ hS_w
            omega

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
