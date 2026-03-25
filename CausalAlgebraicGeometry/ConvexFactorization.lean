/-
  ConvexFactorization.lean — The chain-cover convex factorization theorem

  Given a chain cover L₁,...,L_w of a finite poset C:
  1. Every convex S is determined by (S∩L₁,...,S∩L_w)  [ChainRestriction]
  2. Each S∩Lᵢ is an interval of Lᵢ or empty             [WidthOneProof]
  3. The map is injective with bounded range → |CC| bounded [THIS FILE]

  The factorization is the WIDTH BOUND ENGINE.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import CausalAlgebraicGeometry.CausalAlgebra
import CausalAlgebraicGeometry.ChainRestriction
import CausalAlgebraicGeometry.WidthOneProof

namespace CausalAlgebraicGeometry.ConvexFactorization

open CausalAlgebra ChainRestriction WidthOneProof

/-! ### Local min/max on a chain (no global totality needed) -/

/-- Extract a minimum from a nonempty list where all pairs are comparable. -/
private lemma list_has_min {k : Type*} [Field k] (C : CAlg k)
    (T : Finset C.Λ) (hT : ∀ a ∈ T, ∀ b ∈ T, C.le a b ∨ C.le b a) :
    ∀ (l : List C.Λ), l ≠ [] → (∀ x ∈ l, x ∈ T) →
      ∃ a ∈ l, ∀ x ∈ l, C.le a x := by
  intro l hl hmem
  induction l with
  | nil => exact absurd rfl hl
  | cons y t ih =>
    by_cases ht : t = []
    · exact ⟨y, List.Mem.head _, fun x hx => by
        subst ht; simp [List.mem_cons] at hx; exact hx ▸ C.le_refl _⟩
    · have ht_mem : ∀ x ∈ t, x ∈ T := fun x hx => hmem x (List.mem_cons.mpr (Or.inr hx))
      obtain ⟨a, ha, hmin⟩ := ih ht ht_mem
      have hy_mem : y ∈ T := hmem y (List.Mem.head _)
      have ha_mem : a ∈ T := hmem a (List.mem_cons.mpr (Or.inr ha))
      rcases hT y hy_mem a ha_mem with hya | hay
      · exact ⟨y, List.Mem.head _, fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact C.le_refl _
          · exact C.le_trans _ a x hya (hmin x hx)⟩
      · exact ⟨a, List.mem_cons.mpr (Or.inr ha), fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hay
          · exact hmin x hx⟩

/-- Extract a maximum from a nonempty list where all pairs are comparable. -/
private lemma list_has_max {k : Type*} [Field k] (C : CAlg k)
    (T : Finset C.Λ) (hT : ∀ a ∈ T, ∀ b ∈ T, C.le a b ∨ C.le b a) :
    ∀ (l : List C.Λ), l ≠ [] → (∀ x ∈ l, x ∈ T) →
      ∃ b ∈ l, ∀ x ∈ l, C.le x b := by
  intro l hl hmem
  induction l with
  | nil => exact absurd rfl hl
  | cons y t ih =>
    by_cases ht : t = []
    · exact ⟨y, List.Mem.head _, fun x hx => by
        subst ht; simp [List.mem_cons] at hx; exact hx ▸ C.le_refl _⟩
    · have ht_mem : ∀ x ∈ t, x ∈ T := fun x hx => hmem x (List.mem_cons.mpr (Or.inr hx))
      obtain ⟨b, hb, hmax⟩ := ih ht ht_mem
      have hy_mem : y ∈ T := hmem y (List.Mem.head _)
      have hb_mem : b ∈ T := hmem b (List.mem_cons.mpr (Or.inr hb))
      rcases hT y hy_mem b hb_mem with hyb | hby
      · exact ⟨b, List.mem_cons.mpr (Or.inr hb), fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hyb
          · exact hmax x hx⟩
      · exact ⟨y, List.Mem.head _, fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact C.le_refl _
          · exact C.le_trans x b _ (hmax x hx) hby⟩

/-- Min of a nonempty finset within a chain. -/
private lemma chain_finset_has_min {k : Type*} [Field k] (C : CAlg k)
    (T : Finset C.Λ) (hT : ∀ a ∈ T, ∀ b ∈ T, C.le a b ∨ C.le b a)
    (F : Finset C.Λ) (hF : F ⊆ T) (hne : F.Nonempty) :
    ∃ a ∈ F, ∀ x ∈ F, C.le a x := by
  have hne_list : F.toList ≠ [] := by
    intro h; exact absurd (Finset.toList_eq_nil.mp h ▸ hne) Finset.not_nonempty_empty
  have hmem : ∀ x ∈ F.toList, x ∈ T := fun x hx => hF (Finset.mem_toList.mp hx)
  obtain ⟨a, ha, hmin⟩ := list_has_min C T hT F.toList hne_list hmem
  exact ⟨a, Finset.mem_toList.mp ha, fun x hx => hmin x (Finset.mem_toList.mpr hx)⟩

/-- Max of a nonempty finset within a chain. -/
private lemma chain_finset_has_max {k : Type*} [Field k] (C : CAlg k)
    (T : Finset C.Λ) (hT : ∀ a ∈ T, ∀ b ∈ T, C.le a b ∨ C.le b a)
    (F : Finset C.Λ) (hF : F ⊆ T) (hne : F.Nonempty) :
    ∃ b ∈ F, ∀ x ∈ F, C.le x b := by
  have hne_list : F.toList ≠ [] := by
    intro h; exact absurd (Finset.toList_eq_nil.mp h ▸ hne) Finset.not_nonempty_empty
  have hmem : ∀ x ∈ F.toList, x ∈ T := fun x hx => hF (Finset.mem_toList.mp hx)
  obtain ⟨b, hb, hmax⟩ := list_has_max C T hT F.toList hne_list hmem
  exact ⟨b, Finset.mem_toList.mp hb, fun x hx => hmax x (Finset.mem_toList.mpr hx)⟩

/-! ### Injection bounds domain size -/

/-- If f : α → β is injective and lands in a finset, then |α| ≤ |finset|. -/
theorem injection_bounds_card {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (range : Finset β) (h_range : ∀ a, f a ∈ range) :
    Fintype.card α ≤ range.card := by
  rw [← Finset.card_univ]
  exact Finset.card_le_card_of_injOn f (fun a _ => h_range a)
    (fun a _ b _ hab => hf hab)

/-! ### The factorization theorem -/

/-- **CONVEX FACTORIZATION THEOREM**.

    Given a chain cover, every convex subset is uniquely determined
    by a tuple of intervals (or empty sets), one per chain. -/
theorem convex_factorization {k : Type*} [Field k] (C : CAlg k)
    {w : ℕ} (chains : Fin w → Finset C.Λ)
    (hcover : ∀ x : C.Λ, ∃ i, x ∈ chains i)
    (hchains : ∀ i, IsChainFS C (chains i)) :
    -- (A) Injectivity
    (∀ S₁ S₂ : Finset C.Λ,
      IsConvexFS C S₁ → IsConvexFS C S₂ →
      (∀ i, S₁ ∩ chains i = S₂ ∩ chains i) → S₁ = S₂) ∧
    -- (B) Convexity within each chain
    (∀ i, ∀ S : Finset C.Λ, IsConvexFS C S →
      ∀ a ∈ S ∩ chains i, ∀ b ∈ S ∩ chains i,
        ∀ c ∈ chains i, C.le a c → C.le c b → c ∈ S ∩ chains i) ∧
    -- (C) Each restriction is empty or an interval
    (∀ i, ∀ S : Finset C.Λ, IsConvexFS C S →
      (S ∩ chains i = ∅) ∨
      (∃ a ∈ chains i, ∃ b ∈ chains i, C.le a b ∧
        S ∩ chains i = (chains i).filter (fun c => C.le a c ∧ C.le c b))) :=
  ⟨-- (A) Injectivity
   fun S₁ S₂ _ _ h => chain_decomp_injective C chains hcover S₁ S₂ h,
   -- (B) Convexity within each chain
   fun i S hS a ha b hb c hcL hac hcb =>
     convex_within_chain C S (chains i) hS a b ha hb c hcL hac hcb,
   -- (C) Each restriction is empty or an interval
   fun i S hS => by
     by_cases hne : (S ∩ chains i).Nonempty
     · right
       -- S ∩ chains i is nonempty, lives in chain (totally ordered)
       have hSL_sub : S ∩ chains i ⊆ chains i := Finset.inter_subset_right
       -- Extract min and max using local chain totality
       obtain ⟨a, ha, hmin⟩ := chain_finset_has_min C (chains i)
         (hchains i) (S ∩ chains i) hSL_sub hne
       obtain ⟨b, hb, hmax⟩ := chain_finset_has_max C (chains i)
         (hchains i) (S ∩ chains i) hSL_sub hne
       have haL : a ∈ chains i := hSL_sub ha
       have hbL : b ∈ chains i := hSL_sub hb
       have hab : C.le a b := hmin b hb
       refine ⟨a, haL, b, hbL, hab, ?_⟩
       -- Show: S ∩ chains i = (chains i).filter(a ≤ · ∧ · ≤ b)
       ext c
       simp only [Finset.mem_inter, Finset.mem_filter]
       constructor
       · -- c ∈ S ∩ L → c ∈ L ∧ a ≤ c ∧ c ≤ b
         intro hc
         exact ⟨hc.2, hmin c (Finset.mem_inter.mpr hc),
                       hmax c (Finset.mem_inter.mpr hc)⟩
       · -- c ∈ L ∧ a ≤ c ∧ c ≤ b → c ∈ S ∩ L
         intro ⟨hcL, hac, hcb⟩
         have haS : a ∈ S := (Finset.mem_inter.mp ha).1
         have hbS : b ∈ S := (Finset.mem_inter.mp hb).1
         exact ⟨hS a haS b hbS c hac hcb, hcL⟩
     · left; rwa [Finset.not_nonempty_iff_eq_empty] at hne⟩

end CausalAlgebraicGeometry.ConvexFactorization
