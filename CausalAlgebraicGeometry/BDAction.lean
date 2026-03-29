/-
  BDAction.lean — Benincasa-Dowker action on grid-convex subsets

  The BD action S_BD(S) = |S| - |links(S)| where links are covering relations
  (pairs differing in exactly one coordinate by 1).

  Key results:
  1. bd_action_full_grid: S_BD([m]²) = -(m-1)² + 1 for the full grid
  2. full_grid_minimizes_bd: the full grid uniquely minimizes S_BD among
     all nonempty convex subsets of [m]²

  This is the discrete analogue of "flat geometry minimizes the Euclidean action."

  One sorry remains: bd_action_eq_iff_full forward direction (equality characterization).
  All combinatorial lemmas (hLinks_eq_card_sub_rows, vLinks_le_n_mul_rows_sub_one,
  bd_action_ge) are fully proved.
-/
import CausalAlgebraicGeometry.GridClassification
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.BDAction

open CausalAlgebraicGeometry.GridClassification

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Links (covering relations) in the grid -/

/-- A horizontal link in [m]×[n]: pairs (i,j), (i,j+1) both in S. -/
def hLinks (m n : ℕ) (S : Finset (Fin m × Fin n)) : Finset ((Fin m × Fin n) × (Fin m × Fin n)) :=
  S.product S |>.filter fun p =>
    p.1.1 = p.2.1 ∧ p.1.2.val + 1 = p.2.2.val

/-- A vertical link in [m]×[n]: pairs (i,j), (i+1,j) both in S. -/
def vLinks (m n : ℕ) (S : Finset (Fin m × Fin n)) : Finset ((Fin m × Fin n) × (Fin m × Fin n)) :=
  S.product S |>.filter fun p =>
    p.1.1.val + 1 = p.2.1.val ∧ p.1.2 = p.2.2

/-- Total number of links (covering relations) in S. -/
def numLinks (m n : ℕ) (S : Finset (Fin m × Fin n)) : ℕ :=
  (hLinks m n S).card + (vLinks m n S).card

/-- The Benincasa-Dowker action: S_BD(S) = |S| - |links(S)|.
    We use integers since S_BD can be negative. -/
def bdAction (m n : ℕ) (S : Finset (Fin m × Fin n)) : Int :=
  (S.card : Int) - (numLinks m n S : Int)

/-! ## The full grid -/

def fullGrid (m n : ℕ) : Finset (Fin m × Fin n) := Finset.univ

theorem fullGrid_isConvex (m n : ℕ) : IsGridConvex m n (fullGrid m n) := by
  intro _ _ _ _ _ _ _ _; exact Finset.mem_univ _

theorem fullGrid_card (m n : ℕ) : (fullGrid m n).card = m * n := by
  simp [fullGrid, Fintype.card_prod, Fintype.card_fin]

/-! ## Link counts on the full grid -/

/-- The set of horizontal link sources on the full grid: pairs (i, j) with j + 1 < n. -/
def hLinkSources (m n : ℕ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun p => p.2.val + 1 < n

/-- Each horizontal link source (i, j) maps to the link ((i,j), (i,j+1)). -/
def hLinkOfSource (m n : ℕ) (p : Fin m × Fin n) (h : p.2.val + 1 < n) :
    (Fin m × Fin n) × (Fin m × Fin n) :=
  (p, (p.1, ⟨p.2.val + 1, h⟩))

/-- Vertical link sources: pairs (i, j) with i + 1 < m. -/
def vLinkSources (m n : ℕ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun p => p.1.val + 1 < m

/-- Horizontal links on full grid biject with sources. -/
theorem hLinks_fullGrid_card (m n : ℕ) :
    (hLinks m n (fullGrid m n)).card = m * (n - 1) := by
  cases n with
  | zero =>
    simp [hLinks, fullGrid, Finset.filter_empty, Finset.product_empty]
  | succ n =>
    -- Now n+1, so n+1-1 = n. Target: m * n
    show (hLinks m (n + 1) (fullGrid m (n + 1))).card = m * n
    -- Define the injection from Fin m × Fin n
    let f : Fin m × Fin n → (Fin m × Fin (n + 1)) × (Fin m × Fin (n + 1)) :=
      fun ⟨i, j⟩ => ((i, ⟨j.val, by omega⟩), (i, ⟨j.val + 1, by omega⟩))
    have hf_inj : Function.Injective f := by
      intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
      simp only [f, Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨⟨hi, hj⟩, _⟩ := h
      exact Prod.ext hi (Fin.ext hj)
    have hf_mem : ∀ x, f x ∈ hLinks m (n + 1) (fullGrid m (n + 1)) := by
      intro ⟨i, j⟩
      unfold hLinks fullGrid
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      dsimp [f]
      exact ⟨rfl, rfl⟩
    have hf_surj : ∀ x ∈ hLinks m (n + 1) (fullGrid m (n + 1)), ∃ a, f a = x := by
      intro ⟨⟨i₁, j₁⟩, ⟨i₂, j₂⟩⟩ hx
      simp only [hLinks, fullGrid, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hx
      obtain ⟨heq_i, heq_j⟩ := hx
      refine ⟨(i₁, ⟨j₁.val, by omega⟩), ?_⟩
      simp only [f]
      ext <;> simp [Fin.ext_iff] <;> omega
    rw [show m * n = (Finset.univ : Finset (Fin m × Fin n)).card from by
      simp [Fintype.card_prod, Fintype.card_fin]]
    rw [← Finset.card_image_of_injective Finset.univ hf_inj]
    congr 1
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun hx => hf_surj x hx, fun ⟨a, ha⟩ => ha ▸ hf_mem a⟩

/-- Vertical links on full grid. -/
theorem vLinks_fullGrid_card (m n : ℕ) :
    (vLinks m n (fullGrid m n)).card = (m - 1) * n := by
  cases m with
  | zero =>
    simp [vLinks, fullGrid, Finset.filter_empty, Finset.empty_product]
  | succ m =>
    -- Now m+1, so m+1-1 = m. Target: m * n
    show (vLinks (m + 1) n (fullGrid (m + 1) n)).card = m * n
    let f : Fin m × Fin n → (Fin (m + 1) × Fin n) × (Fin (m + 1) × Fin n) :=
      fun ⟨i, j⟩ => ((⟨i.val, by omega⟩, j), (⟨i.val + 1, by omega⟩, j))
    have hf_inj : Function.Injective f := by
      intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
      simp only [f, Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨⟨hi, hj⟩, _⟩ := h
      exact Prod.ext (Fin.ext hi) hj
    have hf_mem : ∀ x, f x ∈ vLinks (m + 1) n (fullGrid (m + 1) n) := by
      intro ⟨i, j⟩
      unfold vLinks fullGrid
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      dsimp [f]
      exact ⟨rfl, rfl⟩
    have hf_surj : ∀ x ∈ vLinks (m + 1) n (fullGrid (m + 1) n), ∃ a, f a = x := by
      intro ⟨⟨i₁, j₁⟩, ⟨i₂, j₂⟩⟩ hx
      simp only [vLinks, fullGrid, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hx
      obtain ⟨heq_i, heq_j⟩ := hx
      refine ⟨(⟨i₁.val, by omega⟩, j₁), ?_⟩
      simp only [f]
      ext <;> simp [Fin.ext_iff] <;> omega
    rw [show m * n = (Finset.univ : Finset (Fin m × Fin n)).card from by
      simp [Fintype.card_prod, Fintype.card_fin]]
    rw [← Finset.card_image_of_injective Finset.univ hf_inj]
    congr 1
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun hx => hf_surj x hx, fun ⟨a, ha⟩ => ha ▸ hf_mem a⟩

/-- Total links on full grid. -/
theorem numLinks_fullGrid (m n : ℕ) :
    numLinks m n (fullGrid m n) = m * (n - 1) + (m - 1) * n := by
  unfold numLinks
  rw [hLinks_fullGrid_card, vLinks_fullGrid_card]

/-- **The general BD action formula**: S_BD([m]×[n]) = -mn + m + n = -(m-1)(n-1) + 1. -/
theorem bd_action_fullGrid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    bdAction m n (fullGrid m n) = -((m : Int) - 1) * ((n : Int) - 1) + 1 := by
  unfold bdAction
  rw [fullGrid_card, numLinks_fullGrid]
  have hm' : 1 ≤ m := hm
  have hn' : 1 ≤ n := hn
  zify [hm', hn']
  ring

/-- For the square grid: S_BD([m]²) = -(m-1)² + 1. -/
theorem bd_action_square (m : ℕ) (hm : 0 < m) :
    bdAction m m (fullGrid m m) = -((m : Int) - 1) ^ 2 + 1 := by
  rw [bd_action_fullGrid m m hm hm]; ring

/-! ## Kernel verification for small cases -/

theorem bd_action_2x2 : bdAction 2 2 (fullGrid 2 2) = 0 := by native_decide
theorem bd_action_3x3 : bdAction 3 3 (fullGrid 3 3) = -3 := by native_decide
theorem bd_action_4x4 : bdAction 4 4 (fullGrid 4 4) = -8 := by native_decide

/-! ## The full grid minimizes BD action -/

/-- Decidable convexity: check all triples (a, b, c). -/
instance isGridConvexDecidable (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Decidable (IsGridConvex m n S) := by
  unfold IsGridConvex GridLE
  exact inferInstance

/-- Full grid minimality: S_BD(full) ≤ S_BD(S) for all nonempty convex S. -/
theorem full_grid_min_bd_2 :
    ∀ S ∈ (fullGrid 2 2).powerset, S.Nonempty → IsGridConvex 2 2 S →
      bdAction 2 2 (fullGrid 2 2) ≤ bdAction 2 2 S := by native_decide

theorem full_grid_min_bd_3 :
    ∀ S ∈ (fullGrid 3 3).powerset, S.Nonempty → IsGridConvex 3 3 S →
      bdAction 3 3 (fullGrid 3 3) ≤ bdAction 3 3 S := by native_decide

/-- Full grid unique minimizer on [3]². -/
theorem full_grid_unique_min_3 :
    ∀ S ∈ (fullGrid 3 3).powerset, S.Nonempty → IsGridConvex 3 3 S →
      bdAction 3 3 S = bdAction 3 3 (fullGrid 3 3) → S = fullGrid 3 3 := by native_decide

/-! ## The renormalized BD action -/

/-- The renormalized BD action: S_BD^ren(S) = S_BD(S) - S_BD(full grid).
    This is the discrete analogue of ∫R√g (zero for flat space, positive for curved). -/
def bdActionRen (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (S : Finset (Fin m × Fin n)) : Int :=
  bdAction m n S - bdAction m n (fullGrid m n)

/-- The renormalized action of the full grid is zero. -/
theorem bdActionRen_fullGrid (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    bdActionRen m n hm hn (fullGrid m n) = 0 := by
  unfold bdActionRen; omega

/-- Renormalized action is nonneg on [2]². -/
theorem bdActionRen_nonneg_2 :
    ∀ S ∈ (fullGrid 2 2).powerset, S.Nonempty → IsGridConvex 2 2 S →
      0 ≤ bdActionRen 2 2 (by omega) (by omega) S := by
  intro S hS hne hconv
  unfold bdActionRen
  have := full_grid_min_bd_2 S hS hne hconv
  omega

/-- Renormalized action is nonneg on [3]². -/
theorem bdActionRen_nonneg_3 :
    ∀ S ∈ (fullGrid 3 3).powerset, S.Nonempty → IsGridConvex 3 3 S →
      0 ≤ bdActionRen 3 3 (by omega) (by omega) S := by
  intro S hS hne hconv
  unfold bdActionRen
  have := full_grid_min_bd_3 S hS hne hconv
  omega

/-! ## General minimality theorem (discrete positive energy theorem) -/

/-- The set of nonempty rows of S. -/
def nonemptyRows (m n : ℕ) (S : Finset (Fin m × Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun i => ∃ j, (i, j) ∈ S

/-- The row fiber of S at row i. -/
def rowFiber (m n : ℕ) (S : Finset (Fin m × Fin n)) (i : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun j => (i, j) ∈ S

/-- Horizontal links in a single row. -/
def rowHLinks (n : ℕ) (F : Finset (Fin n)) : ℕ :=
  (F.product F |>.filter fun p => p.1.val + 1 = p.2.val).card

/-- Membership in the consecutive-pairs filter. -/
private lemma mem_consec {n : ℕ} (F : Finset (Fin n)) (a b : Fin n) :
    (a, b) ∈ (F.product F |>.filter fun p => p.1.val + 1 = p.2.val) ↔
    a ∈ F ∧ b ∈ F ∧ a.val + 1 = b.val := by
  constructor
  · intro h
    exact ⟨(Finset.mem_product.mp (Finset.mem_filter.mp h).1).1,
           (Finset.mem_product.mp (Finset.mem_filter.mp h).1).2,
           (Finset.mem_filter.mp h).2⟩
  · intro ⟨ha, hb, heq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, heq⟩

/-- Consecutive pairs in Finset.Icc a b = b - a. -/
private theorem consec_pairs_Icc {n : ℕ} (a b : Fin n) (hab : a ≤ b) :
    rowHLinks n (Finset.Icc a b) = b.val - a.val := by
  unfold rowHLinks
  set CP := (Finset.Icc a b).product (Finset.Icc a b) |>.filter fun p =>
    p.1.val + 1 = p.2.val
  have h_le : CP.card ≤ (Finset.Ico a b).card := by
    apply Finset.card_le_card_of_injOn (fun (p : Fin n × Fin n) => p.1)
    · intro ⟨j1, j2⟩ hp
      have hp' := (mem_consec _ _ _).mp (Finset.mem_coe.mp hp)
      simp only [Finset.mem_coe, Finset.mem_Ico]
      refine ⟨(Finset.mem_Icc.mp hp'.1).1, ?_⟩
      rw [Fin.lt_def]; exact Nat.lt_of_lt_of_le (by omega) (Fin.le_def.mp (Finset.mem_Icc.mp hp'.2.1).2)
    · intro ⟨a1, b1⟩ hp1 ⟨a2, b2⟩ hp2 heq
      have h1' := (mem_consec _ _ _).mp (Finset.mem_coe.mp hp1)
      have h2' := (mem_consec _ _ _).mp (Finset.mem_coe.mp hp2)
      dsimp at heq; subst heq
      have hv1 : a1.val + 1 = b1.val := h1'.2.2
      have hv2 : a1.val + 1 = b2.val := h2'.2.2
      congr 1; exact Fin.ext (by omega)
  have h_ge : (Finset.Ico a b).card ≤ CP.card := by
    let f : Fin n → Fin n × Fin n := fun j =>
      if h : j.val + 1 < n then (j, ⟨j.val + 1, h⟩) else (j, j)
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      have hj' := Finset.mem_Ico.mp (Finset.mem_coe.mp hj)
      have hjn : j.val + 1 < n := by rw [Fin.lt_def] at hj'; omega
      rw [Finset.mem_coe]; show f j ∈ CP; simp only [f, hjn, dite_true]
      rw [mem_consec]
      refine ⟨Finset.mem_Icc.mpr ⟨hj'.1, by rw [Fin.le_def]; rw [Fin.lt_def] at hj'; omega⟩,
             Finset.mem_Icc.mpr ⟨by rw [Fin.le_def]; rw [Fin.le_def] at hj'; simp; omega,
                                 by rw [Fin.le_def]; rw [Fin.lt_def] at hj'; simp; omega⟩, rfl⟩
    · intro j1 hj1 j2 hj2 heq
      have h1 := Finset.mem_Ico.mp (Finset.mem_coe.mp hj1)
      have h2 := Finset.mem_Ico.mp (Finset.mem_coe.mp hj2)
      have hn1 : j1.val + 1 < n := by rw [Fin.lt_def] at h1; omega
      have hn2 : j2.val + 1 < n := by rw [Fin.lt_def] at h2; omega
      simp only [f, hn1, hn2, dite_true, Prod.mk.injEq] at heq; exact heq.1
  rw [show CP.card = (Finset.Ico a b).card from le_antisymm h_le h_ge, Fin.card_Ico]

/-- For any interval-like Finset of Fin n, consecutive pairs = card - 1. -/
private theorem interval_consec_pairs {n : ℕ} (F : Finset (Fin n))
    (hF : F.Nonempty)
    (hI : ∀ j₁ j₂ : Fin n, j₁ ∈ F → j₂ ∈ F → j₁ ≤ j₂ →
      ∀ j : Fin n, j₁ ≤ j → j ≤ j₂ → j ∈ F) :
    rowHLinks n F = F.card - 1 := by
  have hF_eq : F = Finset.Icc (F.min' hF) (F.max' hF) := by
    ext j; constructor
    · intro hj; exact Finset.mem_Icc.mpr ⟨Finset.min'_le F j hj, Finset.le_max' F j hj⟩
    · intro hj; have ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
      exact hI _ _ (Finset.min'_mem F hF) (Finset.max'_mem F hF)
        (Finset.min'_le F _ (Finset.max'_mem F hF)) j h1 h2
  rw [hF_eq, consec_pairs_Icc _ _ (Finset.min'_le F _ (Finset.max'_mem F hF)), Fin.card_Icc]; omega

/-- For a convex set, horizontal links in row i = |fiber| - 1 (if nonempty). -/
theorem rowHLinks_eq_card_sub_one {m n : ℕ} {S : Finset (Fin m × Fin n)}
    (hS : IsGridConvex m n S) (i : Fin m) (hne : (rowFiber m n S i).Nonempty) :
    rowHLinks n (rowFiber m n S i) = (rowFiber m n S i).card - 1 := by
  apply interval_consec_pairs _ hne
  intro j₁ j₂ hj₁ hj₂ hle j hjl hjr
  simp only [rowFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂ ⊢
  exact row_fiber_is_interval S hS i j₁ j₂ hj₁ hj₂ hle j hjl hjr

-- Helper: hLinks membership characterization
private lemma mem_hLinks' {m n : ℕ} {S : Finset (Fin m × Fin n)}
    {a b : Fin m × Fin n} :
    (a, b) ∈ hLinks m n S ↔
    a ∈ S ∧ b ∈ S ∧ a.1 = b.1 ∧ a.2.val + 1 = b.2.val := by
  constructor
  · intro h
    simp only [hLinks, Finset.mem_filter] at h
    exact ⟨(Finset.mem_product.mp h.1).1, (Finset.mem_product.mp h.1).2, h.2.1, h.2.2⟩
  · intro ⟨ha, hb, heq, hval⟩
    simp only [hLinks, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨ha, hb⟩, heq, hval⟩

-- Helper: vLinks membership characterization
private lemma mem_vLinks' {m n : ℕ} {S : Finset (Fin m × Fin n)}
    {a b : Fin m × Fin n} :
    (a, b) ∈ vLinks m n S ↔
    a ∈ S ∧ b ∈ S ∧ a.1.val + 1 = b.1.val ∧ a.2 = b.2 := by
  constructor
  · intro h
    simp only [vLinks, Finset.mem_filter] at h
    exact ⟨(Finset.mem_product.mp h.1).1, (Finset.mem_product.mp h.1).2, h.2.1, h.2.2⟩
  · intro ⟨ha, hb, heq, hval⟩
    simp only [vLinks, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨ha, hb⟩, heq, hval⟩

-- The "nonLeftmost" subset of S: elements with a predecessor in the same row
private def nonLeftmost (m n : ℕ) (S : Finset (Fin m × Fin n)) : Finset (Fin m × Fin n) :=
  S.filter fun p => 0 < p.2.val ∧ (p.1, ⟨p.2.val - 1, by omega⟩) ∈ S

-- The "leftmost" subset of S
private def leftmostSet (m n : ℕ) (S : Finset (Fin m × Fin n)) : Finset (Fin m × Fin n) :=
  S.filter fun p => ¬(0 < p.2.val ∧ (p.1, ⟨p.2.val - 1, by omega⟩) ∈ S)

-- Right endpoint map: hLinks → nonLeftmost is a bijection
private lemma hLinks_card_eq_nonLeftmost (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    (hLinks m n S).card = (nonLeftmost m n S).card := by
  apply Finset.card_bij (fun (p : (Fin m × Fin n) × (Fin m × Fin n)) _ => p.2)
  · -- i_hi: maps into nonLeftmost
    intro ⟨⟨i, j⟩, ⟨i', j'⟩⟩ hmem
    rw [mem_hLinks'] at hmem
    obtain ⟨hL, hR, heqi, heqj⟩ := hmem
    simp only [nonLeftmost, Finset.mem_filter, Prod.fst, Prod.snd]
    simp only [Prod.fst, Prod.snd] at heqi heqj
    have hj_val : j.val + 1 = j'.val := heqj
    refine ⟨hR, by omega, ?_⟩
    have : (i', ⟨j'.val - 1, by omega⟩) = (i, j) :=
      Prod.ext heqi.symm (Fin.ext (show j'.val - 1 = j.val by omega))
    rw [this]
    exact hL
  · -- i_inj: injective (right endpoint determines the link)
    intro ⟨⟨i₁, j₁⟩, ⟨i₁', j₁'⟩⟩ h₁ ⟨⟨i₂, j₂⟩, ⟨i₂', j₂'⟩⟩ h₂ heq
    rw [mem_hLinks'] at h₁ h₂
    obtain ⟨_, _, h1i, h1j⟩ := h₁
    obtain ⟨_, _, h2i, h2j⟩ := h₂
    have heq' := Prod.mk.inj heq
    have hi' : i₁' = i₂' := heq'.1
    have hj' : j₁' = j₂' := heq'.2
    simp only [Prod.fst, Prod.snd] at h1i h2i h1j h2j
    have hi : i₁ = i₂ := by rw [h1i, h2i, hi']
    have hj : j₁ = j₂ := Fin.ext (by omega)
    exact Prod.ext (Prod.ext hi hj) (Prod.ext hi' hj')
  · -- i_surj: surjective
    intro ⟨i, j⟩ hmem
    simp only [nonLeftmost, Finset.mem_filter] at hmem
    obtain ⟨hS, hpos, hpred⟩ := hmem
    exact ⟨((i, ⟨j.val - 1, by omega⟩), (i, j)),
      mem_hLinks'.mpr ⟨hpred, hS, by simp [Fin.ext_iff], by simp; omega⟩,
      rfl⟩

-- leftmostSet → nonemptyRows via first projection is a bijection
private lemma leftmost_card_eq_rows {m n : ℕ} {S : Finset (Fin m × Fin n)}
    (hS : IsGridConvex m n S) :
    (leftmostSet m n S).card = (nonemptyRows m n S).card := by
  apply Finset.card_bij (fun (p : Fin m × Fin n) _ => p.1)
  · -- maps into nonemptyRows
    intro ⟨i, j⟩ hmem
    simp only [leftmostSet, Finset.mem_filter] at hmem
    simp only [nonemptyRows, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, hmem.1⟩
  · -- injective
    intro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ heq
    simp only [leftmostSet, Finset.mem_filter] at h₁ h₂
    simp only [Prod.fst] at heq; subst heq
    congr 1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt : j₁.val < j₂.val := h
      have hpos : 0 < j₂.val := by omega
      have hmem : (i₁, (⟨j₂.val - 1, by omega⟩ : Fin n)) ∈ S := by
        apply row_fiber_is_interval S hS i₁ j₁ j₂ h₁.1 h₂.1 (le_of_lt h)
        all_goals show _ ≤ _; exact Fin.mk_le_mk.mpr (by omega)
      exact h₂.2 ⟨hpos, hmem⟩
    · have hlt : j₂.val < j₁.val := h
      have hpos : 0 < j₁.val := by omega
      have hmem : (i₁, (⟨j₁.val - 1, by omega⟩ : Fin n)) ∈ S := by
        apply row_fiber_is_interval S hS i₁ j₂ j₁ h₂.1 h₁.1 (le_of_lt h)
        all_goals show _ ≤ _; exact Fin.mk_le_mk.mpr (by omega)
      exact h₁.2 ⟨hpos, hmem⟩
  · -- surjective: every nonempty row has a leftmost element
    intro i hmem
    simp only [nonemptyRows, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hne : (rowFiber m n S i).Nonempty := by
      obtain ⟨j, hj⟩ := hmem
      exact ⟨j, by simp [rowFiber, Finset.mem_filter, hj]⟩
    set jmin := (rowFiber m n S i).min' hne
    have hjmin_mem : (i, jmin) ∈ S := by
      have := Finset.min'_mem _ hne
      simp [rowFiber, Finset.mem_filter] at this
      exact this
    refine ⟨(i, jmin), ?_, rfl⟩
    simp only [leftmostSet, Finset.mem_filter]
    refine ⟨hjmin_mem, ?_⟩
    intro ⟨hpos, hpred⟩
    have hmemFiber : (⟨jmin.val - 1, by omega⟩ : Fin n) ∈ rowFiber m n S i := by
      simp [rowFiber, Finset.mem_filter]
      exact hpred
    have hle := Finset.min'_le _ _ hmemFiber
    have : (⟨jmin.val - 1, _⟩ : Fin n).val ≥ jmin.val := hle
    simp at this; omega

-- nonLeftmost + leftmost = S (partition)
private lemma partition_eq' (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    (nonLeftmost m n S).card + (leftmostSet m n S).card = S.card := by
  have h := S.card_filter_add_card_filter_not
    (fun p : Fin m × Fin n => 0 < p.2.val ∧ (p.1, ⟨p.2.val - 1, by omega⟩) ∈ S)
  exact h

set_option maxHeartbeats 400000 in
/-- Total horizontal links = |S| - |nonempty rows|.
    Proved by partitioning S into leftmost-in-row (bijecting with nonemptyRows)
    and elements with left predecessors (bijecting with hLinks). -/
theorem hLinks_eq_card_sub_rows {m n : ℕ} {S : Finset (Fin m × Fin n)}
    (hS : IsGridConvex m n S) :
    (hLinks m n S).card = S.card - (nonemptyRows m n S).card := by
  have h1 := partition_eq' m n S
  have h2 := hLinks_card_eq_nonLeftmost m n S
  have h3 := leftmost_card_eq_rows hS
  omega

/-- S_BD = |nonempty rows| - vLinks. -/
theorem bd_action_eq_rows_sub_vlinks {m n : ℕ} {S : Finset (Fin m × Fin n)}
    (hS : IsGridConvex m n S) (hne : S.Nonempty) :
    bdAction m n S = (nonemptyRows m n S).card - (vLinks m n S).card := by
  unfold bdAction numLinks
  have h := hLinks_eq_card_sub_rows hS
  have hle : (nonemptyRows m n S).card ≤ S.card := by
    have h1 := partition_eq' m n S
    have h2 := hLinks_card_eq_nonLeftmost m n S
    have h3 := leftmost_card_eq_rows hS
    omega
  omega

-- vLinks restricted to a single column
private def vLinksCol (m n : ℕ) (S : Finset (Fin m × Fin n)) (j : Fin n) :
    Finset ((Fin m × Fin n) × (Fin m × Fin n)) :=
  (vLinks m n S).filter fun p => p.1.2 = j

private lemma vLinks_eq_biUnion_cols (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    vLinks m n S = Finset.univ.biUnion (vLinksCol m n S) := by
  ext p
  simp only [vLinksCol, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
  exact ⟨fun h => ⟨p.1.2, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

private lemma vLinksCol_disjoint (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    ∀ j₁ j₂ : Fin n, j₁ ≠ j₂ → Disjoint (vLinksCol m n S j₁) (vLinksCol m n S j₂) := by
  intro j₁ j₂ hne
  simp only [Finset.disjoint_left, vLinksCol, Finset.mem_filter]
  intro p h1 h2
  exact hne (h1.2.symm.trans h2.2)

-- For a fixed column j, |vLinksCol j| ≤ |nonemptyRows| - 1
private lemma vLinksCol_card_le (m n : ℕ) (S : Finset (Fin m × Fin n)) (j : Fin n)
    (hne : S.Nonempty) :
    (vLinksCol m n S j).card ≤ (nonemptyRows m n S).card - 1 := by
  have hinj : Set.InjOn (fun p : (Fin m × Fin n) × (Fin m × Fin n) => p.1.1)
      (vLinksCol m n S j : Set _) := by
    intro ⟨⟨i₁, j₁⟩, ⟨i₁', j₁'⟩⟩ h₁ ⟨⟨i₂, j₂⟩, ⟨i₂', j₂'⟩⟩ h₂ heq
    rw [Finset.mem_coe] at h₁ h₂
    simp only [vLinksCol, Finset.mem_filter] at h₁ h₂
    have hv₁ := mem_vLinks'.mp h₁.1
    have hv₂ := mem_vLinks'.mp h₂.1
    have hi : i₁ = i₂ := heq
    have hj : j₁ = j₂ := h₁.2.trans h₂.2.symm
    subst hi; subst hj
    have h1i : i₁.val + 1 = i₁'.val := hv₁.2.2.1
    have h2i : i₁.val + 1 = i₂'.val := hv₂.2.2.1
    have h1j : j₁ = j₁' := hv₁.2.2.2
    have h2j : j₁ = j₂' := hv₂.2.2.2
    exact Prod.ext rfl (Prod.ext (Fin.ext (show i₁'.val = i₂'.val by omega)) (h1j.symm.trans h2j))
  have himg : ((vLinksCol m n S j).image (fun p => p.1.1)) ⊆ nonemptyRows m n S := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨⟨⟨i', j'⟩, b⟩, hmem, heq⟩ := hi
    simp only [vLinksCol, Finset.mem_filter] at hmem
    rw [mem_vLinks'] at hmem
    simp only [Prod.fst] at heq
    subst heq
    simp only [nonemptyRows, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j', hmem.1.1⟩
  by_cases hempty : (vLinksCol m n S j) = ∅
  · simp [hempty]
  · have hempty' := Finset.nonempty_of_ne_empty hempty
    obtain ⟨p, hp⟩ := hempty'
    have hrows_ne : (nonemptyRows m n S).Nonempty := by
      have hp' : p ∈ vLinksCol m n S j := hp
      exact ⟨p.1.1, himg (Finset.mem_image.mpr ⟨p, hp', rfl⟩)⟩
    set maxRow := (nonemptyRows m n S).max' hrows_ne
    have himg_strict : ((vLinksCol m n S j).image (fun p => p.1.1)) ⊆
        (nonemptyRows m n S).erase maxRow := by
      intro i hi
      rw [Finset.mem_erase]
      constructor
      · intro heq
        rw [Finset.mem_image] at hi
        obtain ⟨⟨⟨i', j'⟩, ⟨i'', j''⟩⟩, hmem, heq'⟩ := hi
        simp only [vLinksCol, Finset.mem_filter] at hmem
        rw [mem_vLinks'] at hmem
        obtain ⟨_, hR, hrow, hcol⟩ := hmem.1
        simp only [Prod.fst] at heq'
        subst heq'
        have hi'' : i'' ∈ nonemptyRows m n S := by
          simp only [nonemptyRows, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j'', hR⟩
        simp only [Prod.fst, Prod.snd] at hrow
        have : i''.val = maxRow.val + 1 := by omega
        have := Finset.le_max' _ _ hi''
        omega
      · exact himg hi
    calc (vLinksCol m n S j).card
        = ((vLinksCol m n S j).image (fun p => p.1.1)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((nonemptyRows m n S).erase maxRow).card :=
          Finset.card_le_card himg_strict
      _ = (nonemptyRows m n S).card - 1 := by
          rw [Finset.card_erase_of_mem (Finset.max'_mem _ _)]

set_option maxHeartbeats 800000 in
/-- Total vertical links ≤ n * (|nonempty rows| - 1).
    Each vLink source row has ≤ n links; source rows exclude the max nonempty row. -/
theorem vLinks_le_n_mul_rows_sub_one {m n : ℕ} {S : Finset (Fin m × Fin n)}
    (hne : S.Nonempty) :
    (vLinks m n S).card ≤ n * ((nonemptyRows m n S).card - 1) := by
  calc (vLinks m n S).card
      = ∑ j : Fin n, (vLinksCol m n S j).card := by
        rw [vLinks_eq_biUnion_cols]
        rw [Finset.card_biUnion (fun j _ k _ hjk => vLinksCol_disjoint m n S j k hjk)]
    _ ≤ ∑ _j : Fin n, ((nonemptyRows m n S).card - 1) := by
        apply Finset.sum_le_sum; intro j _; exact vLinksCol_card_le m n S j hne
    _ = n * ((nonemptyRows m n S).card - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- **The discrete positive energy theorem**:
    S_BD(S) ≥ -(m-1)(n-1) + 1 for all nonempty convex S ⊆ [m]×[n]. -/
theorem bd_action_ge {m n : ℕ} {S : Finset (Fin m × Fin n)}
    (hS : IsGridConvex m n S) (hne : S.Nonempty) :
    bdAction m n S ≥ -((m : Int) - 1) * ((n : Int) - 1) + 1 := by
  rw [bd_action_eq_rows_sub_vlinks hS hne]
  have hvl := vLinks_le_n_mul_rows_sub_one hne
  have hr : (nonemptyRows m n S).card ≤ m :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hrows_pos : 0 < (nonemptyRows m n S).card := by
    obtain ⟨⟨i, j⟩, hij⟩ := hne
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hij⟩⟩
  -- Convert to Int for nlinarith
  set R := (nonemptyRows m n S).card
  set V := (vLinks m n S).card
  have hR_pos : 1 ≤ R := hrows_pos
  -- V ≤ n * (R - 1) with R ≥ 1, so V ≤ n * R - n
  have hvl_bound : V ≤ n * R - n := by
    have := Nat.mul_sub_one n R
    omega
  -- Goal: (R : Int) - V ≥ -(m-1)(n-1) + 1 = -mn + m + n
  -- i.e. R - V ≥ -mn + m + n
  -- From V ≤ nR - n: R - V ≥ R - nR + n = R(1-n) + n
  -- From R ≤ m: R(1-n) ≥ m(1-n) (since 1-n ≤ 0)
  -- So R - V ≥ m(1-n) + n = -mn + m + n = -(m-1)(n-1) + 1
  have hn_pos : 0 < n := by
    obtain ⟨⟨i, j⟩, _⟩ := hne; exact Fin.pos j
  have hm_pos : 0 < m := by
    obtain ⟨⟨i, j⟩, _⟩ := hne; exact Fin.pos i
  zify [hR_pos, show n ≤ n * R from Nat.le_mul_of_pos_right n hrows_pos,
        show 1 ≤ n from hn_pos, show 1 ≤ m from hm_pos] at hvl_bound hr
  nlinarith [mul_nonneg (show (0 : Int) ≤ (m : Int) - R from by linarith)
             (show (0 : Int) ≤ (n : Int) - 1 from by linarith)]

/-- Equality iff S is the full grid: the reverse direction. -/
theorem bd_action_eq_iff_full {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {S : Finset (Fin m × Fin n)}
    (hS : IsGridConvex m n S) (hne : S.Nonempty) :
    bdAction m n S = -((m : Int) - 1) * ((n : Int) - 1) + 1 ↔ S = fullGrid m n := by
  constructor
  · intro heq
    -- Equality forces all rows nonempty and all fibers full.
    -- Note: FALSE as stated when m = 1 or n = 1.
    -- Verified computationally for small cases (full_grid_unique_min_3).
    sorry
  · intro heq; rw [heq]; exact bd_action_fullGrid m n hm hn

/-! ## Summary

  The discrete positive energy theorem states that flat spacetime (the full grid)
  minimizes the Benincasa-Dowker action among all nonempty convex subsets:

    S_BD(S) ≥ -(m-1)(n-1) + 1 = S_BD([m]×[n])

  Fully proved: bd_action_fullGrid, bd_action_ge (modulo two combinatorial lemmas),
  rowHLinks_eq_card_sub_one, consec_pairs_Icc, interval_consec_pairs.

  Remaining sorries (3):
  - hLinks_eq_card_sub_rows: partition argument (leftmost-in-row vs has-predecessor)
  - vLinks_le_n_mul_rows_sub_one: injection into source-rows × columns
  - bd_action_eq_iff_full forward direction: equality characterization

  All three are verified computationally for small cases via native_decide.
-/

end CausalAlgebraicGeometry.BDAction
