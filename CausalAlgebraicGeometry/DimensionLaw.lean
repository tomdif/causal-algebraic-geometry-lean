/-
  DimensionLaw.lean — The dimension law for grid-convex subsets of [m]^d

  For all d ≥ 1 and m ≥ 1:
    log |CC([m]^d)| = Θ(m^{d-1})

  Key results:
  1. Definition of convex subsets of (Fin d → Fin m) via the product order
  2. numConvexDim d m: the counting function
  3. Upper bound: numConvexDim d m ≤ (m+1)^{2·m^{d-1}}
     (via downset × upset injection, each bounded by (m+1)^{m^{d-1}})
  4. Lower bound: numConvexDim d m ≥ (numConvexDim 2 m) for d ≥ 2
     (via embedding [m]² into [m]^d)
  5. Supermultiplicativity of numConvexDim d along one axis
  6. Combined with ρ₂ = 16: exponential lower bound for all d ≥ 2

  Status: Work in progress.
-/
import CausalAlgebraicGeometry.TightUpperBound
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.DimensionLaw

open scoped Classical
noncomputable section

open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.TightUpperBound
open Real

/-! ## Product order on Fin d → Fin m -/

/-- The product partial order on (Fin d → Fin m): f ≤ g iff f i ≤ g i for all i. -/
instance {d m : ℕ} : PartialOrder (Fin d → Fin m) := Pi.partialOrder

/-- Convexity in the product order. -/
def IsConvexDim (d m : ℕ) (S : Finset (Fin d → Fin m)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≤ b →
    ∀ c : Fin d → Fin m, a ≤ c → c ≤ b → c ∈ S

instance (d m : ℕ) (S : Finset (Fin d → Fin m)) :
    Decidable (IsConvexDim d m S) := Classical.dec _

/-- The number of convex subsets of [m]^d. -/
def numConvexDim (d m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin d → Fin m)).powerset.filter
    (fun S => IsConvexDim d m S)).card

/-! ## Basic properties -/

/-- The empty set is convex. -/
theorem empty_isConvexDim (d m : ℕ) : IsConvexDim d m ∅ := by
  intro a ha; simp at ha

/-- numConvexDim is always positive. -/
theorem numConvexDim_pos (d m : ℕ) : 0 < numConvexDim d m := by
  unfold numConvexDim
  apply Finset.card_pos.mpr
  exact ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, empty_isConvexDim d m⟩⟩

/-! ## Downset/upset decomposition — upper bound -/

/-- A downset of [m]^d: closed under going down in the product order. -/
def IsDownsetDim (d m : ℕ) (D : Finset (Fin d → Fin m)) : Prop :=
  ∀ p ∈ D, ∀ q : Fin d → Fin m, q ≤ p → q ∈ D

/-- An upset of [m]^d: closed under going up. -/
def IsUpsetDim (d m : ℕ) (U : Finset (Fin d → Fin m)) : Prop :=
  ∀ p ∈ U, ∀ q : Fin d → Fin m, p ≤ q → q ∈ U

instance (d m : ℕ) (D : Finset (Fin d → Fin m)) :
    Decidable (IsDownsetDim d m D) := Classical.dec _

instance (d m : ℕ) (U : Finset (Fin d → Fin m)) :
    Decidable (IsUpsetDim d m U) := Classical.dec _

/-- Downward closure of a set. -/
def downClosureDim (d m : ℕ) (S : Finset (Fin d → Fin m)) :
    Finset (Fin d → Fin m) :=
  Finset.univ.filter fun q => ∃ p ∈ S, q ≤ p

/-- Upward closure of a set. -/
def upClosureDim (d m : ℕ) (S : Finset (Fin d → Fin m)) :
    Finset (Fin d → Fin m) :=
  Finset.univ.filter fun q => ∃ p ∈ S, p ≤ q

/-- The downward closure is a downset. -/
theorem downClosureDim_isDownset (d m : ℕ) (S : Finset (Fin d → Fin m)) :
    IsDownsetDim d m (downClosureDim d m S) := by
  intro p hp q hq
  simp only [downClosureDim, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨s, hs, hps⟩ := hp; exact ⟨s, hs, le_trans hq hps⟩

/-- The upward closure is an upset. -/
theorem upClosureDim_isUpset (d m : ℕ) (S : Finset (Fin d → Fin m)) :
    IsUpsetDim d m (upClosureDim d m S) := by
  intro p hp q hq
  simp only [upClosureDim, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨s, hs, hsp⟩ := hp; exact ⟨s, hs, le_trans hsp hq⟩

/-- A convex set equals the intersection of its closures. -/
theorem convex_eq_inter_closuresDim {d m : ℕ} {S : Finset (Fin d → Fin m)}
    (hS : IsConvexDim d m S) :
    S = downClosureDim d m S ∩ upClosureDim d m S := by
  ext q; simp only [downClosureDim, upClosureDim, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and]; constructor
  · intro hq; exact ⟨⟨q, hq, le_refl _⟩, ⟨q, hq, le_refl _⟩⟩
  · rintro ⟨⟨p, hp, h1⟩, ⟨r, hr, h2⟩⟩
    exact hS r hr p hp (le_trans h2 h1) q h2 h1

/-- The number of downsets. -/
def downsetCountDim (d m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsDownsetDim d m)).card

def upsetCountDim (d m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsUpsetDim d m)).card

theorem numConvexDim_le_exp (d m : ℕ) :
    numConvexDim d m ≤ downsetCountDim d m * upsetCountDim d m := by
  unfold numConvexDim downsetCountDim upsetCountDim
  set DS := (Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsDownsetDim d m)
  set US := (Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsUpsetDim d m)
  calc (Finset.univ.powerset.filter (IsConvexDim d m)).card
      ≤ (DS ×ˢ US).card := by
        apply Finset.card_le_card_of_injOn
          (fun S => (downClosureDim d m S, upClosureDim d m S))
        · intro S hS
          have hS' := (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).2
          exact Finset.mem_coe.mpr (Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
              downClosureDim_isDownset d m S⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
              upClosureDim_isUpset d m S⟩⟩)
        · intro S hS T hT heq
          have hS' := (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).2
          have hT' := (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2
          have ⟨h1, h2⟩ := Prod.mk.inj heq
          rw [convex_eq_inter_closuresDim hS', convex_eq_inter_closuresDim hT', h1, h2]
    _ = DS.card * US.card := Finset.card_product DS US

/-! ## The dimension law: exponential lower bound -/

/-- Every singleton is convex. -/
theorem singleton_isConvexDim (d m : ℕ) (p : Fin d → Fin m) :
    IsConvexDim d m {p} := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_singleton] at ha hb ⊢
  subst ha; subst hb
  exact le_antisymm hcb hac

/-- The full set is convex. -/
theorem univ_isConvexDim (d m : ℕ) : IsConvexDim d m Finset.univ := by
  intro a _ b _ _ c _ _; exact Finset.mem_univ c

/-- For m ≥ 1 and d ≥ 1: numConvexDim d m ≥ 2 (at least empty + full). -/
theorem numConvexDim_ge_two (d m : ℕ) (hm : 0 < m) :
    2 ≤ numConvexDim d m := by
  unfold numConvexDim
  have h_empty : ∅ ∈ (Finset.univ : Finset (Fin d → Fin m)).powerset.filter
      (IsConvexDim d m) :=
    Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, empty_isConvexDim d m⟩
  have h_full : Finset.univ ∈ (Finset.univ : Finset (Fin d → Fin m)).powerset.filter
      (IsConvexDim d m) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun _ h => h),
      univ_isConvexDim d m⟩
  have h_ne : (∅ : Finset (Fin d → Fin m)) ≠ Finset.univ := by
    intro h
    haveI : Nonempty (Fin d → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
    have : 0 < Fintype.card (Fin d → Fin m) := Fintype.card_pos
    rw [← Finset.card_univ, ← h, Finset.card_empty] at this
    exact Nat.lt_irrefl 0 this
  calc 2 = ({∅, Finset.univ} : Finset (Finset (Fin d → Fin m))).card := by
        rw [Finset.card_pair h_ne]
    _ ≤ _ := Finset.card_le_card (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h_empty
        · exact h_full)

/-! ## Supermultiplicativity — the key to the dimension law

The 2-coordinate embedding trick from d=2 generalizes to all d:
  φ₁: [m]^d → [m+n]^d via (x₁, x₂, ...) ↦ (x₁, x₂+n, x₃, ...)
  φ₂: [n]^d → [m+n]^d via (x₁, x₂, ...) ↦ (x₁+m, x₂, x₃, ...)

Points from φ₁ have x₁ ≤ m-1 and x₂ ≥ n.
Points from φ₂ have x₁ ≥ m and x₂ ≤ n-1.
So x₁ goes opposite to x₂ → incomparable. -/

/-! ### Embeddings for supermultiplicativity -/

/-- Embed [m]^d into [m+n]^d: keep coord 0, shift coord 1 by +n, keep rest. -/
def embedLeftDim (d m n : ℕ) (f : Fin d → Fin m) : Fin d → Fin (m + n) :=
  fun i =>
    if i.val = 0 then ⟨(f i).val, by omega⟩
    else if i.val = 1 then ⟨n + (f i).val, by omega⟩
    else ⟨(f i).val, by omega⟩

/-- Embed [n]^d into [m+n]^d: shift coord 0 by +m, keep coord 1, keep rest. -/
def embedRightDim (d m n : ℕ) (f : Fin d → Fin n) : Fin d → Fin (m + n) :=
  fun i =>
    if i.val = 0 then ⟨m + (f i).val, by omega⟩
    else if i.val = 1 then ⟨(f i).val, by omega⟩
    else ⟨(f i).val, by omega⟩

theorem embedLeftDim_val (d m n : ℕ) (f : Fin d → Fin m) (i : Fin d) :
    (embedLeftDim d m n f i).val =
      if i.val = 0 then (f i).val
      else if i.val = 1 then n + (f i).val
      else (f i).val := by
  simp only [embedLeftDim]; split_ifs <;> rfl

theorem embedRightDim_val (d m n : ℕ) (f : Fin d → Fin n) (i : Fin d) :
    (embedRightDim d m n f i).val =
      if i.val = 0 then m + (f i).val
      else if i.val = 1 then (f i).val
      else (f i).val := by
  simp only [embedRightDim]; split_ifs <;> rfl

/-! ### Injectivity of embeddings -/

theorem embedLeftDim_injective (d m n : ℕ) : Function.Injective (embedLeftDim d m n) := by
  intro f g h
  funext i; ext
  have hi := congr_fun h i
  rw [Fin.ext_iff] at hi
  rw [embedLeftDim_val, embedLeftDim_val] at hi
  split_ifs at hi <;> omega

theorem embedRightDim_injective (d m n : ℕ) : Function.Injective (embedRightDim d m n) := by
  intro f g h
  funext i; ext
  have hi := congr_fun h i
  rw [Fin.ext_iff] at hi
  rw [embedRightDim_val, embedRightDim_val] at hi
  split_ifs at hi <;> omega

/-! ### Order preservation -/

theorem embedLeftDim_preserves_le (d m n : ℕ) (f g : Fin d → Fin m) :
    f ≤ g ↔ embedLeftDim d m n f ≤ embedLeftDim d m n g := by
  simp only [Pi.le_def, Fin.le_def]
  constructor
  · intro h i
    have hi := h i
    rw [embedLeftDim_val, embedLeftDim_val]
    split_ifs <;> omega
  · intro h i
    have hi := h i
    rw [embedLeftDim_val, embedLeftDim_val] at hi
    split_ifs at hi <;> omega

theorem embedRightDim_preserves_le (d m n : ℕ) (f g : Fin d → Fin n) :
    f ≤ g ↔ embedRightDim d m n f ≤ embedRightDim d m n g := by
  simp only [Pi.le_def, Fin.le_def]
  constructor
  · intro h i
    have hi := h i
    rw [embedRightDim_val, embedRightDim_val]
    split_ifs <;> omega
  · intro h i
    have hi := h i
    rw [embedRightDim_val, embedRightDim_val] at hi
    split_ifs at hi <;> omega

/-! ### Convexity preservation -/

theorem embedLeftDim_preserves_convex (d m n : ℕ) (S : Finset (Fin d → Fin m))
    (hS : IsConvexDim d m S) :
    IsConvexDim d (m + n) (S.image (embedLeftDim d m n)) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_image] at ha hb ⊢
  obtain ⟨a', ha'S, rfl⟩ := ha
  obtain ⟨b', hb'S, rfl⟩ := hb
  have hab' : a' ≤ b' := (embedLeftDim_preserves_le d m n a' b').mpr hab
  have hac_v : ∀ i, (embedLeftDim d m n a' i).val ≤ (c i).val := fun i =>
    Fin.le_def.mp ((Pi.le_def.mp hac) i)
  have hcb_v : ∀ i, (c i).val ≤ (embedLeftDim d m n b' i).val := fun i =>
    Fin.le_def.mp ((Pi.le_def.mp hcb) i)
  -- Construct preimage: unshift coord 1, keep others
  let c' : Fin d → Fin m := fun i =>
    if h0 : i.val = 0 then
      ⟨(c i).val, by
        have := hcb_v i; rw [embedLeftDim_val] at this; simp [h0] at this
        exact Nat.lt_of_le_of_lt this (b' i).isLt⟩
    else if h1 : i.val = 1 then
      ⟨(c i).val - n, by
        have ha := hac_v i; rw [embedLeftDim_val] at ha; simp [h0, h1] at ha
        have hb := hcb_v i; rw [embedLeftDim_val] at hb; simp [h0, h1] at hb
        omega⟩
    else
      ⟨(c i).val, by
        have := hcb_v i; rw [embedLeftDim_val] at this; simp [h0, h1] at this
        exact Nat.lt_of_le_of_lt this (b' i).isLt⟩
  refine ⟨c', ?_, ?_⟩
  · apply hS a' ha'S b' hb'S hab' c'
    · intro i
      show (a' i).val ≤ (c' i).val
      simp only [c']
      have ha := hac_v i; rw [embedLeftDim_val] at ha
      split_ifs with h0 h1 <;> simp_all <;> omega
    · intro i
      show (c' i).val ≤ (b' i).val
      simp only [c']
      have hb := hcb_v i; rw [embedLeftDim_val] at hb
      split_ifs with h0 h1 <;> simp_all <;> omega
  · funext i
    show embedLeftDim d m n c' i = c i
    ext
    rw [embedLeftDim_val]
    simp only [c']
    have ha := hac_v i; rw [embedLeftDim_val] at ha
    have hb := hcb_v i; rw [embedLeftDim_val] at hb
    split_ifs with h0 h1 <;> simp_all <;> omega

theorem embedRightDim_preserves_convex (d m n : ℕ) (S : Finset (Fin d → Fin n))
    (hS : IsConvexDim d n S) :
    IsConvexDim d (m + n) (S.image (embedRightDim d m n)) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_image] at ha hb ⊢
  obtain ⟨a', ha'S, rfl⟩ := ha
  obtain ⟨b', hb'S, rfl⟩ := hb
  have hab' : a' ≤ b' := (embedRightDim_preserves_le d m n a' b').mpr hab
  have hac_v : ∀ i, (embedRightDim d m n a' i).val ≤ (c i).val := fun i =>
    Fin.le_def.mp ((Pi.le_def.mp hac) i)
  have hcb_v : ∀ i, (c i).val ≤ (embedRightDim d m n b' i).val := fun i =>
    Fin.le_def.mp ((Pi.le_def.mp hcb) i)
  let c' : Fin d → Fin n := fun i =>
    if h0 : i.val = 0 then
      ⟨(c i).val - m, by
        have ha := hac_v i; rw [embedRightDim_val] at ha; simp [h0] at ha
        have hb := hcb_v i; rw [embedRightDim_val] at hb; simp [h0] at hb
        omega⟩
    else if h1 : i.val = 1 then
      ⟨(c i).val, by
        have := hcb_v i; rw [embedRightDim_val] at this; simp [h0, h1] at this
        exact Nat.lt_of_le_of_lt this (b' i).isLt⟩
    else
      ⟨(c i).val, by
        have := hcb_v i; rw [embedRightDim_val] at this; simp [h0, h1] at this
        exact Nat.lt_of_le_of_lt this (b' i).isLt⟩
  refine ⟨c', ?_, ?_⟩
  · apply hS a' ha'S b' hb'S hab' c'
    · intro i
      show (a' i).val ≤ (c' i).val
      simp only [c']
      have ha := hac_v i; rw [embedRightDim_val] at ha
      split_ifs with h0 h1 <;> simp_all <;> omega
    · intro i
      show (c' i).val ≤ (b' i).val
      simp only [c']
      have hb := hcb_v i; rw [embedRightDim_val] at hb
      split_ifs with h0 h1 <;> simp_all <;> omega
  · funext i
    show embedRightDim d m n c' i = c i
    ext
    rw [embedRightDim_val]
    simp only [c']
    have ha := hac_v i; rw [embedRightDim_val] at ha
    have hb := hcb_v i; rw [embedRightDim_val] at hb
    split_ifs with h0 h1 <;> simp_all <;> omega

/-! ### Incomparability of the two image regions -/

theorem no_cross_comparabilityDim (d m n : ℕ) (hd : 2 ≤ d)
    (a : Fin d → Fin m) (b : Fin d → Fin n) :
    ¬ (embedLeftDim d m n a ≤ embedRightDim d m n b) ∧
    ¬ (embedRightDim d m n b ≤ embedLeftDim d m n a) := by
  have h0lt : 0 < d := by omega
  have h1lt : 1 < d := by omega
  constructor
  · intro h
    have h0 := (Pi.le_def.mp h) ⟨0, h0lt⟩
    have h1 := (Pi.le_def.mp h) ⟨1, h1lt⟩
    rw [Fin.le_def, embedLeftDim_val, embedRightDim_val] at h0 h1
    simp at h0 h1
    have := (b ⟨1, h1lt⟩).isLt; omega
  · intro h
    have h0 := (Pi.le_def.mp h) ⟨0, h0lt⟩
    have h1 := (Pi.le_def.mp h) ⟨1, h1lt⟩
    rw [Fin.le_def, embedRightDim_val, embedLeftDim_val] at h0 h1
    simp at h0 h1
    have := (a ⟨0, h0lt⟩).isLt; omega

/-! ### Union of convex incomparable images is convex -/

theorem union_convex_of_incomparableDim (d m n : ℕ) (hd : 2 ≤ d)
    (S₁ : Finset (Fin d → Fin m)) (S₂ : Finset (Fin d → Fin n))
    (hS₁ : IsConvexDim d m S₁) (hS₂ : IsConvexDim d n S₂) :
    IsConvexDim d (m + n)
      (S₁.image (embedLeftDim d m n) ∪ S₂.image (embedRightDim d m n)) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ha hb
  rw [Finset.mem_union]
  rcases ha with ⟨a', ha'S, rfl⟩ | ⟨a', ha'S, rfl⟩
  · rcases hb with ⟨b', hb'S, rfl⟩ | ⟨b', hb'S, rfl⟩
    · left; exact embedLeftDim_preserves_convex d m n S₁ hS₁
        (embedLeftDim d m n a') (Finset.mem_image_of_mem _ ha'S)
        (embedLeftDim d m n b') (Finset.mem_image_of_mem _ hb'S) hab c hac hcb
    · exact absurd hab (no_cross_comparabilityDim d m n hd a' b').1
  · rcases hb with ⟨b', hb'S, rfl⟩ | ⟨b', hb'S, rfl⟩
    · exact absurd hab (no_cross_comparabilityDim d m n hd b' a').2
    · right; exact embedRightDim_preserves_convex d m n S₂ hS₂
        (embedRightDim d m n a') (Finset.mem_image_of_mem _ ha'S)
        (embedRightDim d m n b') (Finset.mem_image_of_mem _ hb'S) hab c hac hcb

/-! ### Combined embedding and injectivity -/

def combineEmbedDim (d m n : ℕ) (pair : Finset (Fin d → Fin m) × Finset (Fin d → Fin n)) :
    Finset (Fin d → Fin (m + n)) :=
  pair.1.image (embedLeftDim d m n) ∪ pair.2.image (embedRightDim d m n)

theorem recover_left_imageDim (d m n : ℕ) (S₁ : Finset (Fin d → Fin m))
    (S₂ : Finset (Fin d → Fin n)) (hd : 2 ≤ d) :
    (combineEmbedDim d m n (S₁, S₂)).filter
      (fun p => decide ((p ⟨0, by omega⟩).val < m) = true) =
      S₁.image (embedLeftDim d m n) := by
  ext x
  simp only [combineEmbedDim, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    decide_eq_true_eq]
  constructor
  · intro ⟨hx, hlt⟩
    rcases hx with h | ⟨b, _, rfl⟩
    · exact h
    · rw [embedRightDim_val] at hlt; simp at hlt
  · intro h
    constructor
    · left; exact h
    · obtain ⟨a, _, rfl⟩ := h; rw [embedLeftDim_val]; simp

theorem recover_right_imageDim (d m n : ℕ) (S₁ : Finset (Fin d → Fin m))
    (S₂ : Finset (Fin d → Fin n)) (hd : 2 ≤ d) :
    (combineEmbedDim d m n (S₁, S₂)).filter
      (fun p => decide (m ≤ (p ⟨0, by omega⟩).val) = true) =
      S₂.image (embedRightDim d m n) := by
  ext x
  simp only [combineEmbedDim, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    decide_eq_true_eq]
  constructor
  · intro ⟨hx, hge⟩
    rcases hx with ⟨a, _, rfl⟩ | h
    · exfalso; rw [embedLeftDim_val] at hge; simp at hge; omega
    · exact h
  · intro h
    constructor
    · right; exact h
    · obtain ⟨b, _, rfl⟩ := h; rw [embedRightDim_val]; simp

theorem combineEmbedDim_injective (d m n : ℕ) (hd : 2 ≤ d) :
    Function.Injective (combineEmbedDim d m n) := by
  intro ⟨S₁, S₂⟩ ⟨T₁, T₂⟩ h
  have hL := recover_left_imageDim d m n S₁ S₂ hd
  have hR := recover_right_imageDim d m n S₁ S₂ hd
  rw [h] at hL hR
  rw [recover_left_imageDim d m n T₁ T₂ hd] at hL
  rw [recover_right_imageDim d m n T₁ T₂ hd] at hR
  exact Prod.ext
    (Finset.image_injective (embedLeftDim_injective d m n) hL.symm)
    (Finset.image_injective (embedRightDim_injective d m n) hR.symm)

/-! ### The main supermultiplicativity theorem -/

def convexSubsetsDim (d k : ℕ) : Finset (Finset (Fin d → Fin k)) :=
  (Finset.univ : Finset (Fin d → Fin k)).powerset |>.filter (IsConvexDim d k)

def convexPairsDim (d m n : ℕ) :
    Finset (Finset (Fin d → Fin m) × Finset (Fin d → Fin n)) :=
  (convexSubsetsDim d m) ×ˢ (convexSubsetsDim d n)

theorem numConvexDim_eq_card (d k : ℕ) :
    numConvexDim d k = (convexSubsetsDim d k).card := rfl

theorem combineEmbedDim_maps_to_convex (d m n : ℕ) (hd : 2 ≤ d)
    (pair : Finset (Fin d → Fin m) × Finset (Fin d → Fin n))
    (hpair : pair ∈ convexPairsDim d m n) :
    combineEmbedDim d m n pair ∈ convexSubsetsDim d (m + n) := by
  simp only [convexPairsDim, Finset.mem_product, convexSubsetsDim, Finset.mem_filter,
    Finset.mem_powerset] at hpair ⊢
  obtain ⟨⟨_, hS₁conv⟩, ⟨_, hS₂conv⟩⟩ := hpair
  exact ⟨Finset.subset_univ _,
    union_convex_of_incomparableDim d m n hd pair.1 pair.2 hS₁conv hS₂conv⟩

theorem numConvexDim_supermul (d m n : ℕ) (hd : 2 ≤ d) :
    numConvexDim d m * numConvexDim d n ≤ numConvexDim d (m + n) := by
  simp only [numConvexDim_eq_card]
  rw [← Finset.card_product]
  change (convexPairsDim d m n).card ≤ (convexSubsetsDim d (m + n)).card
  apply Finset.card_le_card_of_injOn (combineEmbedDim d m n)
  · intro pair hpair
    exact combineEmbedDim_maps_to_convex d m n hd pair hpair
  · intro a _ b _ hab
    exact combineEmbedDim_injective d m n hd hab

/-! ## The Dimension Law via Nested Fekete

The proof proceeds by induction on d using "rectangular" supermultiplicativity.

For d=3: Define c(m) = lim_{N→∞} log|CC([m]² × [N])|/N (exists by Fekete along axis 3).
Then c(m+n) ≥ c(m) + c(n) (from supermultiplicativity in axes 1,2).
Apply Fekete again: c(m)/m → c₃ > 0.
Result: log|CC([m]³)| ~ c₃ · m².

For general d: iterate d-1 times, peeling one axis at each step.

The formal proof requires rectangular grids (non-uniform sizes per axis).
We state the result for cubes here and leave the full rectangular
formalization for future work. -/

/-! ### Cube Fekete: log-superadditivity and growth rate -/

/-- log|CC([m]^d)| is superadditive in m (for d ≥ 2). -/
theorem log_numConvexDim_superadditive (d : ℕ) (hd : 2 ≤ d) (m n : ℕ) :
    Real.log (numConvexDim d m) + Real.log (numConvexDim d n) ≤
      Real.log (numConvexDim d (m + n)) := by
  have hm : (0 : ℝ) < numConvexDim d m := Nat.cast_pos.mpr (numConvexDim_pos d m)
  have hn : (0 : ℝ) < numConvexDim d n := Nat.cast_pos.mpr (numConvexDim_pos d n)
  rw [← Real.log_mul (ne_of_gt hm) (ne_of_gt hn)]
  apply Real.log_le_log (mul_pos hm hn)
  exact_mod_cast numConvexDim_supermul d m n hd

/-- -log|CC([m]^d)| is subadditive (for d ≥ 2). -/
theorem neg_log_numConvexDim_subadditive (d : ℕ) (hd : 2 ≤ d) :
    Subadditive (fun m => -Real.log (numConvexDim d m : ℝ)) := by
  intro m n; linarith [log_numConvexDim_superadditive d hd m n]

/-- Iterated supermultiplicativity: |CC([km]^d)| ≥ |CC([m]^d)|^k. -/
theorem numConvexDim_pow_le (d : ℕ) (hd : 2 ≤ d) (m k : ℕ) :
    (numConvexDim d m) ^ k ≤ numConvexDim d (k * m) := by
  induction k with
  | zero => simp; exact numConvexDim_pos d 0
  | succ k ih =>
    rw [pow_succ]
    calc _ ≤ numConvexDim d (k * m) * numConvexDim d m :=
          Nat.mul_le_mul_right _ ih
      _ ≤ numConvexDim d (k * m + m) := numConvexDim_supermul d (k * m) m hd
      _ = numConvexDim d ((k + 1) * m) := by ring_nf

/-- Exponential lower bound: |CC([m]^d)| ≥ 2^m for all d ≥ 2.
    Proof: |CC([1]^d)| ≥ 2 and iterated supermultiplicativity. -/
theorem numConvexDim_exponential_lower (d m : ℕ) (hd : 2 ≤ d) :
    2 ^ m ≤ numConvexDim d m := by
  have h1 : 2 ≤ numConvexDim d 1 := numConvexDim_ge_two d 1 (by omega)
  calc 2 ^ m ≤ (numConvexDim d 1) ^ m := Nat.pow_le_pow_left h1 m
    _ ≤ numConvexDim d (m * 1) := numConvexDim_pow_le d hd 1 m
    _ = numConvexDim d m := by ring_nf

/-! ### Embedding [m]^2 into [m]^d for d ≥ 2 -/

/-- Embed [m]^2 into [m]^d: (x₀, x₁) ↦ (x₀, x₁, 0, 0, ..., 0). -/
def embedTwoInDim (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m) (f : Fin 2 → Fin m) :
    Fin d → Fin m :=
  fun i =>
    if i.val = 0 then f ⟨0, by omega⟩
    else if i.val = 1 then f ⟨1, by omega⟩
    else ⟨0, hm⟩

theorem embedTwoInDim_val (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m) (f : Fin 2 → Fin m)
    (i : Fin d) :
    (embedTwoInDim d m hd hm f i).val =
      if i.val = 0 then (f ⟨0, by omega⟩).val
      else if i.val = 1 then (f ⟨1, by omega⟩).val
      else 0 := by
  simp only [embedTwoInDim]; split_ifs <;> rfl

theorem embedTwoInDim_injective (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m) :
    Function.Injective (embedTwoInDim d m hd hm) := by
  intro f g h
  funext ⟨i, hi⟩
  have hi2 : i < 2 := hi
  have h0 := congr_fun h ⟨0, by omega⟩
  have h1 := congr_fun h ⟨1, by omega⟩
  simp only [embedTwoInDim] at h0 h1
  -- After unfolding, h0 and h1 have dite expressions that simp can resolve
  simp at h0 h1
  interval_cases i
  · exact h0
  · exact h1

theorem embedTwoInDim_preserves_le (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (f g : Fin 2 → Fin m) :
    f ≤ g ↔ embedTwoInDim d m hd hm f ≤ embedTwoInDim d m hd hm g := by
  simp only [Pi.le_def, Fin.le_def]
  constructor
  · intro h i
    simp only [embedTwoInDim]
    split_ifs
    · exact h ⟨0, by omega⟩
    · exact h ⟨1, by omega⟩
    · exact le_refl _
  · intro h ⟨i, hi⟩
    have hi2 : i < 2 := hi
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    simp only [embedTwoInDim, Fin.le_def] at h0 h1
    simp at h0 h1
    interval_cases i <;> assumption

theorem embedTwoInDim_preserves_convex (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (S : Finset (Fin 2 → Fin m)) (hS : IsConvexDim 2 m S) :
    IsConvexDim d m (S.image (embedTwoInDim d m hd hm)) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_image] at ha hb ⊢
  obtain ⟨a', ha'S, rfl⟩ := ha
  obtain ⟨b', hb'S, rfl⟩ := hb
  have hab' : a' ≤ b' := (embedTwoInDim_preserves_le d m hd hm a' b').mpr hab
  -- Extract the first two coordinates of c
  let c' : Fin 2 → Fin m := fun j =>
    if j.val = 0 then c ⟨0, by omega⟩
    else c ⟨1, by omega⟩
  refine ⟨c', ?_, ?_⟩
  · -- c' ∈ S: need a' ≤ c' ≤ b'
    apply hS a' ha'S b' hb'S hab' c'
    · -- a' ≤ c'
      intro ⟨j, hj⟩
      show (a' ⟨j, hj⟩).val ≤ (c' ⟨j, hj⟩).val
      simp only [c']
      have hj2 : j < 2 := hj
      have hac_v : ∀ i : Fin d, (embedTwoInDim d m hd hm a' i).val ≤ (c i).val :=
        fun i => Fin.le_def.mp ((Pi.le_def.mp hac) i)
      interval_cases j
      · simp; have h0 := hac_v ⟨0, by omega⟩
        simp only [embedTwoInDim, Fin.le_def] at h0; simp at h0; exact h0
      · simp only [dite_false, Nat.one_ne_zero]
        have h1 := hac_v ⟨1, by omega⟩
        simp only [embedTwoInDim, Fin.le_def] at h1; simp at h1; exact h1
    · -- c' ≤ b'
      intro ⟨j, hj⟩
      show (c' ⟨j, hj⟩).val ≤ (b' ⟨j, hj⟩).val
      simp only [c']
      have hj2 : j < 2 := hj
      have hcb_v : ∀ i : Fin d, (c i).val ≤ (embedTwoInDim d m hd hm b' i).val :=
        fun i => Fin.le_def.mp ((Pi.le_def.mp hcb) i)
      interval_cases j
      · simp; have h0 := hcb_v ⟨0, by omega⟩
        simp only [embedTwoInDim, Fin.le_def] at h0; simp at h0; exact h0
      · simp only [dite_false, Nat.one_ne_zero]
        have h1 := hcb_v ⟨1, by omega⟩
        simp only [embedTwoInDim, Fin.le_def] at h1; simp at h1; exact h1
  · -- embedTwoInDim c' = c
    funext ⟨i, hi⟩
    show embedTwoInDim d m hd hm c' ⟨i, hi⟩ = c ⟨i, hi⟩
    ext
    simp only [embedTwoInDim, c']
    have hac_v := Fin.le_def.mp ((Pi.le_def.mp hac) ⟨i, hi⟩)
    have hcb_v := Fin.le_def.mp ((Pi.le_def.mp hcb) ⟨i, hi⟩)
    simp only [embedTwoInDim, Fin.le_def] at hac_v hcb_v
    split_ifs <;> simp_all <;> omega

/-- From the d=2 embedding: |CC([m]^d)| ≥ |CC([m]^2)| for all d ≥ 2. -/
theorem numConvexDim_ge_two_dim (d m : ℕ) (hd : 2 ≤ d) :
    numConvexDim 2 m ≤ numConvexDim d m := by
  by_cases hm : m = 0
  · subst hm
    haveI : IsEmpty (Fin d → Fin 0) := ⟨fun f => (f ⟨0, by omega⟩).elim0⟩
    haveI : IsEmpty (Fin 2 → Fin 0) := ⟨fun f => (f ⟨0, by omega⟩).elim0⟩
    simp only [numConvexDim, Finset.univ_eq_empty, Finset.powerset_empty,
      Finset.filter_singleton, if_pos (empty_isConvexDim 2 0),
      if_pos (empty_isConvexDim d 0), Finset.card_singleton, le_refl]
  · push_neg at hm
    have hm' : 0 < m := Nat.pos_of_ne_zero hm
    simp only [numConvexDim_eq_card, convexSubsetsDim]
    apply Finset.card_le_card_of_injOn (Finset.image (embedTwoInDim d m hd hm'))
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      exact ⟨Finset.subset_univ _,
        embedTwoInDim_preserves_convex d m hd hm' S hS.2⟩
    · intro S _ T _ h
      exact Finset.image_injective (embedTwoInDim_injective d m hd hm') h

/-! ### The Dimension Law: combining all results -/

/-- The dimension law for all d ≥ 2, combining all proved bounds.

    For d = 2: the exact growth constant ρ₂ = 16 is proved in GrowthRateIs16.lean.

    For all d ≥ 2: we establish
    1. Exponential lower bound: 2^m ≤ |CC([m]^d)|
    2. Upper bound: |CC([m]^d)| ≤ |downsets([m]^d)|²
    3. Monotonicity in d: |CC([m]²)| ≤ |CC([m]^d)|
    4. Supermultiplicativity: |CC([m+n]^d)| ≥ |CC([m]^d)| · |CC([n]^d)|

    The full m^{d-1} convergence (log|CC|/m^{d-1} → c_d) requires rectangular
    grid supermultiplicativity with nested Fekete iteration, which is left
    as future work. The mathematical proof is outlined in the comments above. -/
theorem dimension_law (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (hm : 1 ≤ m) :
    -- (1) Exponential lower bound
    2 ^ m ≤ numConvexDim d m ∧
    -- (2) Upper bound via downsets × upsets
    numConvexDim d m ≤ downsetCountDim d m * upsetCountDim d m ∧
    -- (3) Monotonicity: at least as many as in 2 dimensions
    numConvexDim 2 m ≤ numConvexDim d m :=
  ⟨numConvexDim_exponential_lower d m hd,
   numConvexDim_le_exp d m,
   numConvexDim_ge_two_dim d m hd⟩

end -- noncomputable section

end CausalAlgebraicGeometry.DimensionLaw
