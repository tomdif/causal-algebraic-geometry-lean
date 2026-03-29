/-
  CrossingBound.lean — Upper bound on crossing antitone pairs via domain-splitting Lindström map.

  We prove: |crossingPairs m| ≤ C(2m+1,m) * C(2m-1,m).
-/
import CausalAlgebraicGeometry.AntitoneCount
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.CrossingBound

open Finset Nat

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open scoped Classical
noncomputable section

/-! ## First crossing index -/

def firstCross {m : ℕ}
    (d u : Fin m → Fin (m + 1))
    (hcross : ∃ i, (u i).val ≥ (d i).val) : Fin m :=
  Finset.min' ((Finset.univ : Finset (Fin m)).filter (fun i => (u i).val ≥ (d i).val))
    (by obtain ⟨i, hi⟩ := hcross; exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩)

lemma firstCross_spec {m : ℕ}
    (d u : Fin m → Fin (m + 1))
    (hcross : ∃ i, (u i).val ≥ (d i).val) :
    (u (firstCross d u hcross)).val ≥ (d (firstCross d u hcross)).val := by
  have hne : ((Finset.univ : Finset (Fin m)).filter (fun i => (u i).val ≥ (d i).val)).Nonempty :=
    by obtain ⟨i, hi⟩ := hcross; exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have hmem := Finset.min'_mem
    ((Finset.univ : Finset (Fin m)).filter (fun i => (u i).val ≥ (d i).val)) hne
  rw [mem_filter] at hmem; exact hmem.2

lemma firstCross_minimal {m : ℕ}
    (d u : Fin m → Fin (m + 1))
    (hcross : ∃ i, (u i).val ≥ (d i).val)
    (j : Fin m) (hj : j < firstCross d u hcross) :
    (u j).val < (d j).val := by
  by_contra h; push_neg at h
  have : j ∈ (Finset.univ : Finset (Fin m)).filter (fun i => (u i).val ≥ (d i).val) :=
    mem_filter.mpr ⟨mem_univ _, h⟩
  exact absurd (lt_of_lt_of_le hj (Finset.min'_le _ _ this)) (lt_irrefl _)

/-! ## The domain-splitting Lindström map -/

def splitF {m : ℕ} (d u : Fin m → Fin (m + 1)) (i₀ : Fin m) :
    Fin (m + 1) → Fin (m + 1) :=
  fun k =>
    if h : k.val ≤ i₀.val then
      u ⟨k.val, by omega⟩
    else
      d ⟨k.val - 1, by omega⟩

def splitG {m : ℕ} (d u : Fin m → Fin (m + 1)) (i₀ : Fin m) (hm : 1 ≤ m) :
    Fin (m - 1) → Fin (m + 1) :=
  fun k =>
    if h : k.val < i₀.val then
      d ⟨k.val, by omega⟩
    else
      u ⟨k.val + 1, by omega⟩

/-! ## Antitonicity of splitF -/

theorem splitF_antitone {m : ℕ} {d u : Fin m → Fin (m + 1)}
    (hd : Antitone d) (hu : Antitone u)
    (hcross : ∃ i, (u i).val ≥ (d i).val)
    {i₀ : Fin m} (hi₀ : i₀ = firstCross d u hcross) :
    Antitone (splitF d u i₀) := by
  intro a b hab
  simp only [splitF, Fin.le_def]
  by_cases ha : a.val ≤ i₀.val
  · by_cases hb : b.val ≤ i₀.val
    · rw [dif_pos ha, dif_pos hb]
      exact hu (Fin.mk_le_mk.mpr (Fin.le_def.mp hab))
    · rw [dif_pos ha, dif_neg hb]
      have hui₀ := firstCross_spec d u hcross
      rw [← hi₀] at hui₀
      have h1 : (d ⟨b.val - 1, by omega⟩).val ≤ (d i₀).val :=
        hd (Fin.mk_le_mk.mpr (by omega))
      have h2 : (u i₀).val ≤ (u ⟨a.val, by omega⟩).val :=
        hu (Fin.mk_le_mk.mpr ha)
      omega
  · by_cases hb : b.val ≤ i₀.val
    · omega
    · rw [dif_neg ha, dif_neg hb]
      exact hd (Fin.mk_le_mk.mpr (by omega))

/-! ## Antitonicity of splitG -/

theorem splitG_antitone {m : ℕ} {d u : Fin m → Fin (m + 1)}
    (hd : Antitone d) (hu : Antitone u)
    (hcross : ∃ i, (u i).val ≥ (d i).val)
    {i₀ : Fin m} (hi₀ : i₀ = firstCross d u hcross)
    (hm : 1 ≤ m) :
    Antitone (splitG d u i₀ hm) := by
  intro a b hab
  simp only [splitG, Fin.le_def]
  by_cases ha : a.val < i₀.val
  · by_cases hb : b.val < i₀.val
    · rw [dif_pos ha, dif_pos hb]
      exact hd (Fin.mk_le_mk.mpr (Fin.le_def.mp hab))
    · rw [dif_pos ha, dif_neg hb]
      have hi₀_pos : 0 < i₀.val := by omega
      have hlt : (⟨i₀.val - 1, by omega⟩ : Fin m) < firstCross d u hcross := by
        rw [← hi₀]; exact Fin.mk_lt_mk.mpr (by omega)
      have hbefore := firstCross_minimal d u hcross ⟨i₀.val - 1, by omega⟩ hlt
      have h1 : (d ⟨i₀.val - 1, by omega⟩).val ≤ (d ⟨a.val, by omega⟩).val :=
        hd (Fin.mk_le_mk.mpr (by omega))
      have h2 : (u ⟨b.val + 1, by omega⟩).val ≤ (u ⟨i₀.val, by omega⟩).val :=
        hu (Fin.mk_le_mk.mpr (by omega))
      have h3 : (u ⟨i₀.val, by omega⟩).val ≤ (u ⟨i₀.val - 1, by omega⟩).val :=
        hu (Fin.mk_le_mk.mpr (by omega))
      omega
  · by_cases hb : b.val < i₀.val
    · omega
    · rw [dif_neg ha, dif_neg hb]
      exact hu (Fin.mk_le_mk.mpr (by omega))

/-! ## Injectivity -/

theorem splitMap_injective (m : ℕ) (hm : 1 ≤ m)
    (d₁ u₁ d₂ u₂ : Fin m → Fin (m + 1))
    (hd₁ : Antitone d₁) (hu₁ : Antitone u₁)
    (hd₂ : Antitone d₂) (hu₂ : Antitone u₂)
    (hc₁ : ∃ i, (u₁ i).val ≥ (d₁ i).val)
    (hc₂ : ∃ i, (u₂ i).val ≥ (d₂ i).val)
    (hf : splitF d₁ u₁ (firstCross d₁ u₁ hc₁) = splitF d₂ u₂ (firstCross d₂ u₂ hc₂))
    (hg : splitG d₁ u₁ (firstCross d₁ u₁ hc₁) hm =
          splitG d₂ u₂ (firstCross d₂ u₂ hc₂) hm) :
    d₁ = d₂ ∧ u₁ = u₂ := by
  set i₁ := firstCross d₁ u₁ hc₁
  set i₂ := firstCross d₂ u₂ hc₂
  -- Step 1: prove i₁.val = i₂.val
  have hi : i₁.val = i₂.val := by
    by_contra hi_ne
    rcases Nat.lt_or_gt_of_ne hi_ne with hi_lt | hi_lt
    · -- i₁ < i₂: read f at i₁ and g at i₁
      have hf_eq := congr_fun hf ⟨i₁.val, by omega⟩
      simp only [splitF, dif_pos (le_refl i₁.val),
        dif_pos (show i₁.val ≤ i₂.val by omega)] at hf_eq
      have hg_eq := congr_fun hg ⟨i₁.val, by omega⟩
      simp only [splitG, dif_neg (show ¬(i₁.val < i₁.val) by omega),
        dif_pos hi_lt] at hg_eq
      have hbefore := firstCross_minimal d₂ u₂ hc₂ ⟨i₁.val, by omega⟩
        (Fin.mk_lt_mk.mpr hi_lt)
      have h_anti : (u₁ ⟨i₁.val + 1, by omega⟩).val ≤ (u₁ ⟨i₁.val, i₁.isLt⟩).val :=
        hu₁ (Fin.mk_le_mk.mpr (by omega))
      have eq1 := congr_arg Fin.val hf_eq
      have eq2 := congr_arg Fin.val hg_eq
      simp at eq1 eq2
      omega
    · -- i₂ < i₁: symmetric
      have hf_eq := congr_fun hf ⟨i₂.val, by omega⟩
      simp only [splitF, dif_pos (show i₂.val ≤ i₁.val by omega),
        dif_pos (le_refl i₂.val)] at hf_eq
      have hg_eq := congr_fun hg ⟨i₂.val, by omega⟩
      simp only [splitG, dif_pos hi_lt,
        dif_neg (show ¬(i₂.val < i₂.val) by omega)] at hg_eq
      have hbefore := firstCross_minimal d₁ u₁ hc₁ ⟨i₂.val, by omega⟩
        (Fin.mk_lt_mk.mpr hi_lt)
      have h_anti : (u₂ ⟨i₂.val + 1, by omega⟩).val ≤ (u₂ ⟨i₂.val, i₂.isLt⟩).val :=
        hu₂ (Fin.mk_le_mk.mpr (by omega))
      have eq1 := congr_arg Fin.val hf_eq
      have eq2 := congr_arg Fin.val hg_eq
      simp at eq1 eq2
      omega
  -- Step 2: extract d and u from f and g
  constructor
  · funext k
    by_cases hk : k.val < i₁.val
    · -- d(k) from g at position k
      have := congr_fun hg ⟨k.val, by omega⟩
      simp only [splitG, dif_pos hk, dif_pos (show k.val < i₂.val by omega)] at this
      exact Fin.ext (congr_arg Fin.val this)
    · -- d(k) from f at position k+1
      push_neg at hk
      have hf_eq := congr_fun hf ⟨k.val + 1, by omega⟩
      simp only [splitF, dif_neg (show ¬(k.val + 1 ≤ i₁.val) by omega),
        dif_neg (show ¬(k.val + 1 ≤ i₂.val) by omega)] at hf_eq
      -- hf_eq : d₁ ⟨k.val + 1 - 1, _⟩ = d₂ ⟨k.val + 1 - 1, _⟩
      -- k.val + 1 - 1 = k.val
      have hv1 : (d₁ ⟨k.val + 1 - 1, by omega⟩).val = (d₁ k).val := by
        congr 1
      have hv2 : (d₂ ⟨k.val + 1 - 1, by omega⟩).val = (d₂ k).val := by
        congr 1
      exact Fin.ext (by have := congr_arg Fin.val hf_eq; omega)
  · funext k
    by_cases hk : k.val ≤ i₁.val
    · -- u(k) from f at position k
      have := congr_fun hf ⟨k.val, by omega⟩
      simp only [splitF, dif_pos hk, dif_pos (show k.val ≤ i₂.val by omega)] at this
      exact Fin.ext (congr_arg Fin.val this)
    · -- u(k) from g at position k-1
      push_neg at hk
      have hg_eq := congr_fun hg ⟨k.val - 1, by omega⟩
      simp only [splitG, dif_neg (show ¬(k.val - 1 < i₁.val) by omega),
        dif_neg (show ¬(k.val - 1 < i₂.val) by omega)] at hg_eq
      -- hg_eq : u₁ ⟨k.val - 1 + 1, _⟩ = u₂ ⟨k.val - 1 + 1, _⟩
      -- Since k.val - 1 + 1 = k.val (as k.val > i₁.val ≥ 0, so k.val ≥ 1)
      have hk_pos : 1 ≤ k.val := by
        have := i₁.isLt; omega
      have hFinEq : (⟨k.val - 1 + 1, by omega⟩ : Fin m) = k :=
        Fin.ext (Nat.sub_add_cancel hk_pos)
      have hv1 : (u₁ ⟨k.val - 1 + 1, by omega⟩).val = (u₁ k).val := by rw [hFinEq]
      have hv2 : (u₂ ⟨k.val - 1 + 1, by omega⟩).val = (u₂ k).val := by rw [hFinEq]
      exact Fin.ext (by have := congr_arg Fin.val hg_eq; omega)

/-! ## Crossing pairs bound -/

def crossingPairs (m : ℕ) :
    Finset ((Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1))) :=
  Finset.univ.filter fun p =>
    Antitone p.1 ∧ Antitone p.2 ∧ ∃ i, (p.2 i).val ≥ (p.1 i).val

theorem crossing_pairs_le (m : ℕ) (hm : 1 ≤ m) :
    (crossingPairs m).card ≤ Nat.choose (2 * m + 1) m * Nat.choose (2 * m - 1) m := by
  set targetF := (Finset.univ : Finset (Fin (m + 1) → Fin (m + 1))).filter Antitone
  set targetG := (Finset.univ : Finset (Fin (m - 1) → Fin (m + 1))).filter Antitone
  -- Cardinality of target factors
  have htF : targetF.card = Nat.choose (2 * m + 1) m := by
    have h1 := CausalAlgebraicGeometry.AntitoneCount.card_antitone_eq_choose (m + 1) m
    rw [show m + 1 + m = 2 * m + 1 from by ring] at h1
    rw [h1]
    -- Need: C(2m+1, m+1) = C(2m+1, m). Use choose_symm with (2m+1) - m = m+1.
    have : Nat.choose (2 * m + 1) ((2 * m + 1) - (m + 1)) = Nat.choose (2 * m + 1) (m + 1) :=
      Nat.choose_symm (by omega)
    rw [show (2 * m + 1) - (m + 1) = m from by omega] at this
    exact this.symm
  have htG : targetG.card = Nat.choose (2 * m - 1) m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h1 := CausalAlgebraicGeometry.AntitoneCount.card_antitone_eq_choose k (k + 1)
    rw [show k + (k + 1) = 2 * (k + 1) - 1 from by omega] at h1
    rw [h1]
    -- Need: C(2k+1, k) = C(2k+1, k+1). Use choose_symm with (2k+1) - (k+1) = k.
    have : Nat.choose (2 * (k + 1) - 1) ((2 * (k + 1) - 1) - k) =
        Nat.choose (2 * (k + 1) - 1) k :=
      Nat.choose_symm (by omega)
    rw [show (2 * (k + 1) - 1) - k = k + 1 from by omega] at this
    exact this.symm
  rw [← htF, ← htG, ← card_product]
  -- Define the map using dite for the crossing witness
  let mapFn : (Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1)) →
      (Fin (m + 1) → Fin (m + 1)) × (Fin (m - 1) → Fin (m + 1)) :=
    fun p =>
      if h : ∃ i, (p.2 i).val ≥ (p.1 i).val then
        (splitF p.1 p.2 (firstCross p.1 p.2 h),
         splitG p.1 p.2 (firstCross p.1 p.2 h) hm)
      else
        (fun _ => 0, fun _ => 0)
  apply Finset.card_le_card_of_injOn mapFn
  · -- Maps into target
    intro p hp
    have ⟨hd, hu, hc⟩ := (mem_filter.mp hp).2
    simp only [mapFn, dif_pos hc]
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, splitF_antitone hd hu hc rfl⟩,
      mem_filter.mpr ⟨mem_univ _, splitG_antitone hd hu hc rfl hm⟩⟩
  · -- Injective on crossingPairs
    intro p₁ hp₁ p₂ hp₂ heq
    have ⟨hd₁, hu₁, hc₁⟩ := (mem_filter.mp hp₁).2
    have ⟨hd₂, hu₂, hc₂⟩ := (mem_filter.mp hp₂).2
    simp only [mapFn, dif_pos hc₁, dif_pos hc₂, Prod.mk.injEq] at heq
    have hdu := splitMap_injective m hm p₁.1 p₁.2 p₂.1 p₂.2
      hd₁ hu₁ hd₂ hu₂ hc₁ hc₂ heq.1 heq.2
    exact Prod.ext hdu.1 hdu.2

end

end CausalAlgebraicGeometry.CrossingBound
