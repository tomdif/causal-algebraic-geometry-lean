/-
  MonotoneProfileBound.lean — numGridConvex m m ≤ 32^m
  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.Supermultiplicativity
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Fin

namespace CausalAlgebraicGeometry.MonotoneProfileBound

open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GridClassification

/-! ## Strictly monotone Fin functions are determined by their image -/

theorem strictMono_eq_of_image_eq {N m : ℕ} {φ ψ : Fin m → Fin N}
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (heq : Finset.univ.image φ = Finset.univ.image ψ) : φ = ψ := by
  funext i
  have hφi : φ i ∈ Finset.univ.image ψ :=
    heq ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hφi
  suffices k = i by subst this; exact hk.symm
  have count_φ : ((Finset.univ.image φ).filter (· ≤ φ i)).card = i.val + 1 := by
    rw [Finset.filter_image,
      show Finset.univ.filter (fun x => φ x ≤ φ i) = Finset.Iic i from by
        ext j; simp [Finset.mem_Iic, hφ.le_iff_le],
      Finset.card_image_of_injective _ hφ.injective, Fin.card_Iic]
  have count_ψ : ((Finset.univ.image ψ).filter (· ≤ ψ k)).card = k.val + 1 := by
    rw [Finset.filter_image,
      show Finset.univ.filter (fun x => ψ x ≤ ψ k) = Finset.Iic k from by
        ext j; simp [Finset.mem_Iic, hψ.le_iff_le],
      Finset.card_image_of_injective _ hψ.injective, Fin.card_Iic]
  have : ((Finset.univ.image φ).filter (· ≤ φ i)).card =
      ((Finset.univ.image ψ).filter (· ≤ ψ k)).card := by rw [heq, hk]
  ext; omega

/-! ## Closures and convexity -/

def downClosure (m : ℕ) (S : Finset (Fin m × Fin m)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun q => ∃ p ∈ S, q.1 ≤ p.1 ∧ q.2 ≤ p.2

def upClosure (m : ℕ) (S : Finset (Fin m × Fin m)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun q => ∃ p ∈ S, p.1 ≤ q.1 ∧ p.2 ≤ q.2

theorem convex_eq_inter_closures {m : ℕ} {S : Finset (Fin m × Fin m)}
    (hS : IsGridConvex m m S) : S = downClosure m S ∩ upClosure m S := by
  ext q; simp only [downClosure, upClosure, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and]; constructor
  · intro hq; exact ⟨⟨q, hq, le_refl _, le_refl _⟩, ⟨q, hq, le_refl _, le_refl _⟩⟩
  · rintro ⟨⟨p, hp, h1, h2⟩, ⟨r, hr, h3, h4⟩⟩
    exact hS r hr p hp ⟨le_trans h3 h1, le_trans h4 h2⟩ q ⟨h3, h4⟩ ⟨h1, h2⟩

/-! ## Downsets, upsets, boundaries -/

def IsDownset (m : ℕ) (D : Finset (Fin m × Fin m)) : Prop :=
  ∀ p ∈ D, ∀ q : Fin m × Fin m, q.1 ≤ p.1 → q.2 ≤ p.2 → q ∈ D

def IsUpset (m : ℕ) (U : Finset (Fin m × Fin m)) : Prop :=
  ∀ p ∈ U, ∀ q : Fin m × Fin m, p.1 ≤ q.1 → p.2 ≤ q.2 → q ∈ U

instance (m : ℕ) (D : Finset (Fin m × Fin m)) : Decidable (IsDownset m D) := by
  unfold IsDownset; exact inferInstance

instance (m : ℕ) (U : Finset (Fin m × Fin m)) : Decidable (IsUpset m U) := by
  unfold IsUpset; exact inferInstance

theorem downClosure_isDownset (m : ℕ) (S : Finset (Fin m × Fin m)) :
    IsDownset m (downClosure m S) := by
  intro p hp q hq1 hq2
  simp only [downClosure, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨s, hs, h1, h2⟩ := hp; exact ⟨s, hs, le_trans hq1 h1, le_trans hq2 h2⟩

theorem upClosure_isUpset (m : ℕ) (S : Finset (Fin m × Fin m)) :
    IsUpset m (upClosure m S) := by
  intro p hp q hq1 hq2
  simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨s, hs, h1, h2⟩ := hp; exact ⟨s, hs, le_trans h1 hq1, le_trans h2 hq2⟩

/-- Downset from boundary function. -/
def downsetOfBdy (m : ℕ) (b : Fin m → Fin (m + 1)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => p.2.val < (b p.1).val

theorem downsetOfBdy_mem {m : ℕ} {b : Fin m → Fin (m + 1)} {i : Fin m} {j : Fin m} :
    (i, j) ∈ downsetOfBdy m b ↔ j.val < (b i).val := by
  simp [downsetOfBdy]

theorem downsetOfBdy_isDownset {m : ℕ} {b : Fin m → Fin (m + 1)} (hb : Antitone b) :
    IsDownset m (downsetOfBdy m b) := by
  intro p hp q hq1 hq2
  rw [downsetOfBdy_mem] at hp ⊢
  have : (b p.1).val ≤ (b q.1).val := by
    have h := hb hq1; rw [Fin.le_def] at h; exact h
  have : q.2.val ≤ p.2.val := hq2
  omega

theorem downsetOfBdy_injective (m : ℕ) : Function.Injective (downsetOfBdy m) := by
  intro b₁ b₂ h; funext i; ext; by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt <;> {
    have h1 : min (b₁ i).val (b₂ i).val < m := by
      have := (b₁ i).isLt; have := (b₂ i).isLt; omega
    have hmem₁ : (i, ⟨min (b₁ i).val (b₂ i).val, h1⟩) ∈ downsetOfBdy m b₁ ↔
        (i, ⟨min (b₁ i).val (b₂ i).val, h1⟩) ∈ downsetOfBdy m b₂ := by rw [h]
    simp [downsetOfBdy_mem] at hmem₁; omega }

/-- Row fiber card equals boundary value. -/
theorem card_row_eq_bdy {m : ℕ} (b : Fin m → Fin (m + 1)) (i : Fin m) :
    ((Finset.univ : Finset (Fin m)).filter (fun j => (i, j) ∈ downsetOfBdy m b)).card =
      (b i).val := by
  have hbi : (b i).val ≤ m := Nat.lt_add_one_iff.mp (b i).isLt
  -- Rewrite to filter by j.val < (b i).val
  have h1 : (Finset.univ : Finset (Fin m)).filter (fun j => (i, j) ∈ downsetOfBdy m b) =
      (Finset.univ : Finset (Fin m)).filter (fun j => j.val < (b i).val) := by
    ext j; simp [downsetOfBdy_mem]
  rw [h1]
  rcases Nat.eq_or_lt_of_le hbi with h_eq | h_lt
  · -- (b i).val = m: filter is all of univ
    have h2 : (Finset.univ : Finset (Fin m)).filter (fun j : Fin m => j.val < (b i).val) =
        Finset.univ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _; have := j.isLt; omega
    rw [h2, Finset.card_univ, Fintype.card_fin, h_eq]
  · -- (b i).val < m: use Finset.Iio
    have h2 : (Finset.univ : Finset (Fin m)).filter (fun j : Fin m => j.val < (b i).val) =
        Finset.Iio (⟨(b i).val, h_lt⟩ : Fin m) := by
      ext j; simp [Finset.mem_Iio, Fin.lt_def]
    rw [h2, Fin.card_Iio]

/-- Every downset has a boundary representation. -/
theorem exists_bdy {m : ℕ} (D : Finset (Fin m × Fin m)) (hD : IsDownset m D) :
    ∃ b : Fin m → Fin (m + 1), Antitone b ∧ D = downsetOfBdy m b := by
  refine ⟨fun i => ⟨((Finset.univ : Finset (Fin m)).filter (fun j => (i, j) ∈ D)).card,
    by have := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j => (i, j) ∈ D)
       simp [Finset.card_univ, Fintype.card_fin] at this; omega⟩, ?_, ?_⟩
  · -- Antitone
    intro i i' h; rw [Fin.le_def]; simp only
    exact Finset.card_le_card (fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hD _ hj _ h (le_refl _))
  · -- D = downsetOfBdy
    ext ⟨i, j⟩; rw [downsetOfBdy_mem]; simp only; constructor
    · -- (i,j) ∈ D → j.val < card
      intro hmem
      have : Finset.Iic j ⊆ (Finset.univ : Finset (Fin m)).filter (fun j' => (i, j') ∈ D) := by
        intro j' hj'; rw [Finset.mem_Iic] at hj'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hD _ hmem _ (le_refl _) hj'
      have h_card := Finset.card_le_card this
      rw [Fin.card_Iic] at h_card; omega
    · -- j.val < card → (i,j) ∈ D
      intro hlt; by_contra hne
      have : (Finset.univ : Finset (Fin m)).filter (fun j' => (i, j') ∈ D) ⊆ Finset.Iio j := by
        intro j' hj'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
        rw [Finset.mem_Iio]; exact lt_of_not_ge (fun hge => hne (hD _ hj' _ (le_refl _) hge))
      have h_card := Finset.card_le_card this
      rw [Fin.card_Iio] at h_card; omega

/-! ## Antitone encoding -/

def antitoneEncode (m : ℕ) (f : Fin m → Fin (m + 1)) : Finset (Fin (2 * m)) :=
  Finset.univ.image (fun i : Fin m =>
    (⟨(m - (f i).val) + i.val, by have := (f i).isLt; omega⟩ : Fin (2 * m)))

theorem antitoneEncode_strictMono {m : ℕ} {f : Fin m → Fin (m + 1)} (hf : Antitone f) :
    StrictMono (fun i : Fin m =>
      (⟨(m - (f i).val) + i.val, by have := (f i).isLt; omega⟩ : Fin (2 * m))) := by
  intro a b hab; rw [Fin.lt_def]; simp only
  have h1 : (f b).val ≤ (f a).val := by have := hf (le_of_lt hab); rwa [Fin.le_def] at this
  have h2 := (f a).isLt; have h3 := (f b).isLt; omega

theorem antitoneEncode_injOn (m : ℕ) :
    Set.InjOn (antitoneEncode m) {f | Antitone f} := by
  intro f hf g hg heq
  have := strictMono_eq_of_image_eq (antitoneEncode_strictMono hf) (antitoneEncode_strictMono hg) heq
  funext i; have hi := congr_fun this i; rw [Fin.ext_iff] at hi; simp only at hi
  ext; omega

theorem card_antitone_le (m : ℕ) :
    ((Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone).card ≤ 4 ^ m := by
  calc ((Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone).card
      ≤ Fintype.card (Finset (Fin (2 * m))) := by
        rw [← Finset.card_univ (α := Finset (Fin (2 * m)))]
        exact Finset.card_le_card_of_injOn (antitoneEncode m)
          (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
          (fun f hf g hg h => antitoneEncode_injOn m
            (show Antitone f from (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2)
            (show Antitone g from (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2) h)
    _ = 2 ^ Fintype.card (Fin (2 * m)) := Fintype.card_finset
    _ = 2 ^ (2 * m) := by rw [Fintype.card_fin]
    _ = 4 ^ m := by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]

/-! ## Counting downsets and upsets -/

theorem card_downsets_le (m : ℕ) :
    ((Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m)).card ≤ 4 ^ m := by
  -- Define boundary map: D ↦ (fun i => card of row filter)
  set bdy : Finset (Fin m × Fin m) → (Fin m → Fin (m + 1)) :=
    fun D i => ⟨((Finset.univ : Finset (Fin m)).filter (fun j => (i, j) ∈ D)).card,
      by have := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j => (i, j) ∈ D)
         simp [Finset.card_univ, Fintype.card_fin] at this; omega⟩ with bdy_def
  -- The boundary map sends downsets to antitone functions
  have h_maps : ∀ D ∈ (Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m),
      bdy D ∈ (Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone := by
    intro D hD
    rw [Finset.mem_filter, Finset.mem_powerset] at hD
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i i' hii' => by
      rw [Fin.le_def]; simp only [bdy]
      exact Finset.card_le_card (fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hD.2 _ hj _ hii' (le_refl _))⟩
  -- The boundary map is injective on downsets
  have h_inj : ∀ D₁ ∈ (Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m),
      ∀ D₂ ∈ (Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m),
      bdy D₁ = bdy D₂ → D₁ = D₂ := by
    intro D₁ hD₁ D₂ hD₂ heq
    rw [Finset.mem_filter, Finset.mem_powerset] at hD₁ hD₂
    obtain ⟨b₁, _, h₁⟩ := exists_bdy D₁ hD₁.2
    obtain ⟨b₂, _, h₂⟩ := exists_bdy D₂ hD₂.2
    rw [h₁, h₂]; congr 1; funext i; ext
    have hi := congr_fun heq i; rw [Fin.ext_iff] at hi; simp only [bdy] at hi
    rw [h₁, h₂, card_row_eq_bdy, card_row_eq_bdy] at hi; exact hi
  -- Combine: |downsets| ≤ |antitone functions| ≤ 4^m
  calc _ ≤ ((Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone).card := by
        apply Finset.card_le_card_of_injOn bdy
          (fun D hD => Finset.mem_coe.mpr (h_maps D hD))
          (fun D₁ hD₁ D₂ hD₂ heq =>
            h_inj D₁ (Finset.mem_coe.mp hD₁) D₂ (Finset.mem_coe.mp hD₂) heq)
    _ ≤ 4 ^ m := card_antitone_le m

theorem card_upsets_le (m : ℕ) :
    ((Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsUpset m)).card ≤ 4 ^ m := by
  -- Inject upsets into downsets via complement: U ↦ univ \ U
  calc _ ≤ ((Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m)).card := by
        apply Finset.card_le_card_of_injOn (fun U => Finset.univ \ U)
          (fun U hU => by
            have hU' := Finset.mem_filter.mp (Finset.mem_coe.mp hU)
            exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
              ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, fun p hp q hq1 hq2 => by
                rw [Finset.mem_sdiff] at hp ⊢
                exact ⟨Finset.mem_univ _, fun hq => hp.2 (hU'.2 q hq p hq1 hq2)⟩⟩))
          (fun U₁ _ U₂ _ heq => by
            have heq' : Finset.univ \ U₁ = Finset.univ \ U₂ := heq
            have key : ∀ p, p ∈ Finset.univ \ U₁ ↔ p ∈ Finset.univ \ U₂ := fun p => by
              rw [heq']
            ext p; constructor <;> intro hp <;> by_contra hnp
            · exact ((key p).mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnp⟩) |>
                Finset.mem_sdiff.mp).2 hp
            · exact ((key p).mp (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnp⟩) |>
                Finset.mem_sdiff.mp).2 hp)
    _ ≤ 4 ^ m := card_downsets_le m

/-! ## Main bound -/

theorem numGridConvex_le_exp (m : ℕ) : numGridConvex m m ≤ 32 ^ m := by
  suffices h : numGridConvex m m ≤ 16 ^ m from
    le_trans h (Nat.pow_le_pow_left (by omega) m)
  -- Inject convex sets into downsets × upsets
  unfold numGridConvex
  set DS := (Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m)
  set US := (Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsUpset m)
  calc (Finset.univ.powerset.filter (IsGridConvex m m)).card
      ≤ (DS ×ˢ US).card := by
        apply Finset.card_le_card_of_injOn (fun S => (downClosure m S, upClosure m S))
          (fun S hS => by
            have hS' := Finset.mem_coe.mp hS
            rw [Finset.mem_filter, Finset.mem_powerset] at hS'
            exact Finset.mem_coe.mpr (Finset.mem_product.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
                downClosure_isDownset m S⟩,
               Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
                upClosure_isUpset m S⟩⟩))
          (fun S hS T hT heq => by
            have hS' := (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).2
            have hT' := (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2
            have ⟨h1, h2⟩ := Prod.mk.inj heq
            rw [convex_eq_inter_closures hS', convex_eq_inter_closures hT', h1, h2])
    _ = DS.card * US.card := Finset.card_product DS US
    _ ≤ 4 ^ m * 4 ^ m := Nat.mul_le_mul (card_downsets_le m) (card_upsets_le m)
    _ = (4 * 4) ^ m := by rw [Nat.mul_pow]
    _ = 16 ^ m := by congr 1

end CausalAlgebraicGeometry.MonotoneProfileBound
