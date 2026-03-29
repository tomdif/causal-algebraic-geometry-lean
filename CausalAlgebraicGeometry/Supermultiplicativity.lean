/-
  Supermultiplicativity.lean — |CC([(m+n)]²)| ≥ |CC([m]²)| · |CC([n]²)|

  The number of order-convex subsets of the grid poset [k]×[k] is supermultiplicative:
  given convex S₁ ⊆ [m]² and convex S₂ ⊆ [n]², we embed them into disjoint,
  incomparable regions of [(m+n)]² whose union is again convex.
  The map (S₁, S₂) ↦ φ₁(S₁) ∪ φ₂(S₂) is injective, proving the inequality.

  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.GridClassification
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Prod

namespace CausalAlgebraicGeometry.Supermultiplicativity

open CausalAlgebraicGeometry.GridClassification

/-! ## Decidability for IsGridConvex -/

instance isGridConvexDecidable (m n : ℕ) (S : Finset (Fin m × Fin n)) :
    Decidable (IsGridConvex m n S) := by
  unfold IsGridConvex GridLE
  exact inferInstance

/-! ## Counting function -/

/-- The number of order-convex subsets of Fin m × Fin n. -/
def numGridConvex (m n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin n)).powerset).filter
    (fun S => IsGridConvex m n S) |>.card

/-! ## The embeddings

  φ₁(i, j) = (i, j + n) — rows [0, m), columns [n, m+n)
  φ₂(i, j) = (i + m, j) — rows [m, m+n), columns [0, n)

  We construct these directly using Fin.mk to avoid type mismatches with
  Fin.natAdd/castAdd which produce Fin (n + m) instead of Fin (m + n).
-/

/-- Embed [m]² into [(m+n)]² via (i, j) ↦ (i, j+n). -/
def embedLeft (m n : ℕ) (p : Fin m × Fin m) : Fin (m + n) × Fin (m + n) :=
  (⟨p.1.val, by omega⟩, ⟨n + p.2.val, by omega⟩)

/-- Embed [n]² into [(m+n)]² via (i, j) ↦ (i+m, j). -/
def embedRight (m n : ℕ) (p : Fin n × Fin n) : Fin (m + n) × Fin (m + n) :=
  (⟨m + p.1.val, by omega⟩, ⟨p.2.val, by omega⟩)

/-! ## Key value lemmas -/

@[simp] theorem embedLeft_fst_val (m n : ℕ) (p : Fin m × Fin m) :
    (embedLeft m n p).1.val = p.1.val := rfl

@[simp] theorem embedLeft_snd_val (m n : ℕ) (p : Fin m × Fin m) :
    (embedLeft m n p).2.val = n + p.2.val := rfl

@[simp] theorem embedRight_fst_val (m n : ℕ) (p : Fin n × Fin n) :
    (embedRight m n p).1.val = m + p.1.val := rfl

@[simp] theorem embedRight_snd_val (m n : ℕ) (p : Fin n × Fin n) :
    (embedRight m n p).2.val = p.2.val := rfl

/-! ## Injectivity -/

theorem embedLeft_injective (m n : ℕ) : Function.Injective (embedLeft m n) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only [embedLeft, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := Fin.val_eq_of_eq h1
  have h2' := Fin.val_eq_of_eq h2
  simp at h1' h2'
  exact Prod.ext (Fin.ext h1') (Fin.ext (by omega))

theorem embedRight_injective (m n : ℕ) : Function.Injective (embedRight m n) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only [embedRight, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := Fin.val_eq_of_eq h1
  have h2' := Fin.val_eq_of_eq h2
  simp at h1' h2'
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext h2')

/-! ## Ordering preservation -/

theorem embedLeft_preserves_le (m n : ℕ) (a b : Fin m × Fin m) :
    GridLE m m a b ↔ GridLE (m + n) (m + n) (embedLeft m n a) (embedLeft m n b) := by
  simp only [GridLE, Fin.le_def, embedLeft_fst_val, embedLeft_snd_val]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

theorem embedRight_preserves_le (m n : ℕ) (a b : Fin n × Fin n) :
    GridLE n n a b ↔ GridLE (m + n) (m + n) (embedRight m n a) (embedRight m n b) := by
  simp only [GridLE, Fin.le_def, embedRight_fst_val, embedRight_snd_val]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · intro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/-! ## Convexity preservation -/

theorem embedLeft_preserves_convex (m n : ℕ) (S : Finset (Fin m × Fin m))
    (hS : IsGridConvex m m S) :
    IsGridConvex (m + n) (m + n) (S.image (embedLeft m n)) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_image] at ha hb ⊢
  obtain ⟨a', ha'S, rfl⟩ := ha
  obtain ⟨b', hb'S, rfl⟩ := hb
  have hab' : GridLE m m a' b' := (embedLeft_preserves_le m n a' b').mpr hab
  -- Bounds on c
  have hc1_lt : c.1.val < m := by
    have := hcb.1; simp only [Fin.le_def, embedLeft_fst_val] at this
    exact Nat.lt_of_le_of_lt this b'.1.isLt
  have hc2_ge : n ≤ c.2.val := by
    have := hac.2; simp only [Fin.le_def, embedLeft_snd_val] at this; omega
  have hc2_sub_lt : c.2.val - n < m := by omega
  -- Construct preimage
  let c' : Fin m × Fin m := (⟨c.1.val, hc1_lt⟩, ⟨c.2.val - n, hc2_sub_lt⟩)
  refine ⟨c', ?_, ?_⟩
  · apply hS a' ha'S b' hb'S hab' c'
    · -- a' ≤ c'
      constructor
      · show a'.1.val ≤ c.1.val
        have := hac.1; simp only [Fin.le_def, embedLeft_fst_val] at this; exact this
      · show a'.2.val ≤ c.2.val - n
        have := hac.2; simp only [Fin.le_def, embedLeft_snd_val] at this; omega
    · -- c' ≤ b'
      constructor
      · show c.1.val ≤ b'.1.val
        have := hcb.1; simp only [Fin.le_def, embedLeft_fst_val] at this; exact this
      · show c.2.val - n ≤ b'.2.val
        have := hcb.2; simp only [Fin.le_def, embedLeft_snd_val] at this; omega
  · -- embedLeft c' = c
    show embedLeft m n c' = c
    ext
    · simp [embedLeft, c']
    · simp [embedLeft, c']; omega

theorem embedRight_preserves_convex (m n : ℕ) (S : Finset (Fin n × Fin n))
    (hS : IsGridConvex n n S) :
    IsGridConvex (m + n) (m + n) (S.image (embedRight m n)) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_image] at ha hb ⊢
  obtain ⟨a', ha'S, rfl⟩ := ha
  obtain ⟨b', hb'S, rfl⟩ := hb
  have hab' : GridLE n n a' b' := (embedRight_preserves_le m n a' b').mpr hab
  -- Bounds on c
  have hc1_ge : m ≤ c.1.val := by
    have := hac.1; simp only [Fin.le_def, embedRight_fst_val] at this; omega
  have hc2_lt : c.2.val < n := by
    have := hcb.2; simp only [Fin.le_def, embedRight_snd_val] at this
    exact Nat.lt_of_le_of_lt this b'.2.isLt
  have hc1_sub_lt : c.1.val - m < n := by omega
  -- Construct preimage
  let c' : Fin n × Fin n := (⟨c.1.val - m, hc1_sub_lt⟩, ⟨c.2.val, hc2_lt⟩)
  refine ⟨c', ?_, ?_⟩
  · apply hS a' ha'S b' hb'S hab' c'
    · constructor
      · show a'.1.val ≤ c.1.val - m
        have := hac.1; simp only [Fin.le_def, embedRight_fst_val] at this; omega
      · show a'.2.val ≤ c.2.val
        have := hac.2; simp only [Fin.le_def, embedRight_snd_val] at this; exact this
    · constructor
      · show c.1.val - m ≤ b'.1.val
        have := hcb.1; simp only [Fin.le_def, embedRight_fst_val] at this; omega
      · show c.2.val ≤ b'.2.val
        have := hcb.2; simp only [Fin.le_def, embedRight_snd_val] at this; exact this
  · show embedRight m n c' = c
    ext
    · simp [embedRight, c']; omega
    · simp [embedRight, c']

/-! ## No cross-comparability -/

theorem no_cross_comparability (m n : ℕ) (a : Fin m × Fin m) (b : Fin n × Fin n) :
    ¬ GridLE (m + n) (m + n) (embedLeft m n a) (embedRight m n b) ∧
    ¬ GridLE (m + n) (m + n) (embedRight m n b) (embedLeft m n a) := by
  simp only [GridLE, Fin.le_def, embedLeft_fst_val, embedLeft_snd_val,
    embedRight_fst_val, embedRight_snd_val, not_and]
  constructor
  · intro _; have := b.2.isLt; omega
  · intro _; have := a.1.isLt; omega

/-! ## Union of convex incomparable sets is convex -/

theorem union_convex_of_incomparable (m n : ℕ)
    (S₁ : Finset (Fin m × Fin m)) (S₂ : Finset (Fin n × Fin n))
    (hS₁ : IsGridConvex m m S₁) (hS₂ : IsGridConvex n n S₂) :
    IsGridConvex (m + n) (m + n)
      (S₁.image (embedLeft m n) ∪ S₂.image (embedRight m n)) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ha hb
  rw [Finset.mem_union]
  rcases ha with ⟨a', ha'S, rfl⟩ | ⟨a', ha'S, rfl⟩
  · rcases hb with ⟨b', hb'S, rfl⟩ | ⟨b', hb'S, rfl⟩
    · left; exact embedLeft_preserves_convex m n S₁ hS₁
        (embedLeft m n a') (Finset.mem_image_of_mem _ ha'S)
        (embedLeft m n b') (Finset.mem_image_of_mem _ hb'S) hab c hac hcb
    · exact absurd hab (no_cross_comparability m n a' b').1
  · rcases hb with ⟨b', hb'S, rfl⟩ | ⟨b', hb'S, rfl⟩
    · exact absurd hab (no_cross_comparability m n b' a').2
    · right; exact embedRight_preserves_convex m n S₂ hS₂
        (embedRight m n a') (Finset.mem_image_of_mem _ ha'S)
        (embedRight m n b') (Finset.mem_image_of_mem _ hb'S) hab c hac hcb

/-! ## The combined embedding and its injectivity -/

def combineEmbed (m n : ℕ) (pair : Finset (Fin m × Fin m) × Finset (Fin n × Fin n)) :
    Finset (Fin (m + n) × Fin (m + n)) :=
  pair.1.image (embedLeft m n) ∪ pair.2.image (embedRight m n)

theorem recover_left_image (m n : ℕ) (S₁ : Finset (Fin m × Fin m))
    (S₂ : Finset (Fin n × Fin n)) :
    (combineEmbed m n (S₁, S₂)).filter (fun p => decide (p.1.val < m) = true) =
      S₁.image (embedLeft m n) := by
  ext x
  simp only [combineEmbed, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    decide_eq_true_eq]
  constructor
  · intro ⟨hx, hlt⟩
    rcases hx with h | ⟨b, _, rfl⟩
    · exact h
    · simp at hlt; omega
  · intro h
    constructor
    · left; exact h
    · obtain ⟨a, _, rfl⟩ := h; simp [embedLeft]

theorem recover_right_image (m n : ℕ) (S₁ : Finset (Fin m × Fin m))
    (S₂ : Finset (Fin n × Fin n)) :
    (combineEmbed m n (S₁, S₂)).filter (fun p => decide (m ≤ p.1.val) = true) =
      S₂.image (embedRight m n) := by
  ext x
  simp only [combineEmbed, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    decide_eq_true_eq]
  constructor
  · intro ⟨hx, hge⟩
    rcases hx with ⟨a, _, rfl⟩ | h
    · simp at hge; omega
    · exact h
  · intro h
    constructor
    · right; exact h
    · obtain ⟨b, _, rfl⟩ := h; simp [embedRight]

theorem combineEmbed_injective (m n : ℕ) :
    Function.Injective (combineEmbed m n) := by
  intro ⟨S₁, S₂⟩ ⟨T₁, T₂⟩ h
  have hL := recover_left_image m n S₁ S₂
  have hR := recover_right_image m n S₁ S₂
  rw [h] at hL hR
  rw [recover_left_image] at hL
  rw [recover_right_image] at hR
  exact Prod.ext
    (Finset.image_injective (embedLeft_injective m n) hL.symm)
    (Finset.image_injective (embedRight_injective m n) hR.symm)

/-! ## The main theorem -/

def convexSubsets (k : ℕ) : Finset (Finset (Fin k × Fin k)) :=
  (Finset.univ : Finset (Fin k × Fin k)).powerset |>.filter (IsGridConvex k k)

def convexPairs (m n : ℕ) : Finset (Finset (Fin m × Fin m) × Finset (Fin n × Fin n)) :=
  (convexSubsets m) ×ˢ (convexSubsets n)

theorem combineEmbed_maps_to_convex (m n : ℕ)
    (pair : Finset (Fin m × Fin m) × Finset (Fin n × Fin n))
    (hpair : pair ∈ convexPairs m n) :
    combineEmbed m n pair ∈ convexSubsets (m + n) := by
  simp only [convexPairs, Finset.mem_product, convexSubsets, Finset.mem_filter,
    Finset.mem_powerset] at hpair ⊢
  obtain ⟨⟨_, hS₁conv⟩, ⟨_, hS₂conv⟩⟩ := hpair
  exact ⟨Finset.subset_univ _, union_convex_of_incomparable m n pair.1 pair.2 hS₁conv hS₂conv⟩

theorem numGridConvex_eq_convexSubsets_card (k : ℕ) :
    numGridConvex k k = (convexSubsets k).card := rfl

/-- **Supermultiplicativity of grid-convex subset counts.**

    |CC([(m+n)]²)| ≥ |CC([m]²)| · |CC([n]²)| -/
theorem supermultiplicativity (m n : ℕ) :
    numGridConvex m m * numGridConvex n n ≤ numGridConvex (m + n) (m + n) := by
  simp only [numGridConvex_eq_convexSubsets_card]
  rw [← Finset.card_product]
  change (convexPairs m n).card ≤ (convexSubsets (m + n)).card
  apply Finset.card_le_card_of_injOn (combineEmbed m n)
  · intro pair hpair
    exact combineEmbed_maps_to_convex m n pair hpair
  · intro a _ b _ hab
    exact combineEmbed_injective m n hab

end CausalAlgebraicGeometry.Supermultiplicativity
