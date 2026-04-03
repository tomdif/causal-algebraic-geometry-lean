/-
  HeightBijection.lean — Downsets of [m]^{d+1} biject with antitone functions.

  MAIN RESULT: downsetCountDim(d+1, m) = #{antitone (Fin d → Fin m) → Fin(m+1)}

  Zero sorry.
-/
import CausalAlgebraicGeometry.SlabCharacterization

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000

namespace CausalAlgebraicGeometry.HeightBijection

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.SlicingBound
open CausalAlgebraicGeometry.SlabCharacterization

noncomputable section
open scoped Classical

/-! ## subGraph: antitone function → downset -/

/-- Build a downset from an antitone height function. -/
def subGraph (d m : ℕ) (φ : (Fin d → Fin m) → Fin (m + 1)) :
    Finset (Fin (d + 1) → Fin m) :=
  Finset.univ.filter fun p =>
    (p ⟨d, by omega⟩).val < (φ (fun i : Fin d => p ⟨i.val, by omega⟩)).val

/-- Membership in subGraph via extendByZ. -/
theorem mem_subGraph_ext {d m : ℕ} (φ : (Fin d → Fin m) → Fin (m + 1))
    (f : Fin d → Fin m) (k : Fin m) :
    extendByZ d m f k ∈ subGraph d m φ ↔ k.val < (φ f).val := by
  simp only [subGraph, Finset.mem_filter, Finset.mem_univ, true_and]
  have hf : (fun i : Fin d => (extendByZ d m f k) ⟨i.val, by omega⟩) = f := by
    funext i; exact extendByZ_init d m f k i
  have hk : (extendByZ d m f k) ⟨d, by omega⟩ = k := extendByZ_last d m f k
  constructor
  · intro h; rwa [hf, hk] at h
  · intro h; rw [hf, hk]; exact h

theorem subGraph_isDownset {d m : ℕ} {φ : (Fin d → Fin m) → Fin (m + 1)}
    (hφ : Antitone φ) : IsDownsetDim (d + 1) m (subGraph d m φ) := by
  intro p hp q hqp
  simp only [subGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  have hbase : (fun i : Fin d => q ⟨i.val, by omega⟩) ≤
               (fun i : Fin d => p ⟨i.val, by omega⟩) :=
    fun i => hqp ⟨i.val, by omega⟩
  calc (q ⟨d, by omega⟩).val
      ≤ (p ⟨d, by omega⟩).val := Fin.le_def.mp (hqp ⟨d, by omega⟩)
    _ < (φ (fun i => p ⟨i.val, by omega⟩)).val := hp
    _ ≤ (φ (fun i => q ⟨i.val, by omega⟩)).val := Fin.le_def.mp (hφ hbase)

theorem subGraph_injective (d m : ℕ) :
    Function.Injective (subGraph d m :
      ((Fin d → Fin m) → Fin (m + 1)) → Finset (Fin (d + 1) → Fin m)) := by
  intro φ ψ h
  funext f
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · have hk : (φ f).val < m := by omega
    have h1 : extendByZ d m f ⟨(φ f).val, hk⟩ ∈ subGraph d m ψ :=
      (mem_subGraph_ext ψ f _).mpr hlt
    have h2 : ¬ (extendByZ d m f ⟨(φ f).val, hk⟩ ∈ subGraph d m φ) := by
      rw [mem_subGraph_ext]; simp [Fin.lt_def]
    rw [h] at h2; exact h2 h1
  · have hk : (ψ f).val < m := by omega
    have h1 : extendByZ d m f ⟨(ψ f).val, hk⟩ ∈ subGraph d m φ :=
      (mem_subGraph_ext φ f _).mpr hgt
    have h2 : ¬ (extendByZ d m f ⟨(ψ f).val, hk⟩ ∈ subGraph d m ψ) := by
      rw [mem_subGraph_ext]; simp [Fin.lt_def]
    rw [← h] at h2; exact h2 h1

/-! ## heightFun: downset → antitone function -/

def heightFun (d m : ℕ) (D : Finset (Fin (d + 1) → Fin m)) (f : Fin d → Fin m) :
    Fin (m + 1) :=
  ⟨(fiber d m D f).card, by
    calc (fiber d m D f).card ≤ Finset.card Finset.univ := Finset.card_filter_le _ _
      _ = m := Finset.card_fin m
      _ < m + 1 := by omega⟩

theorem heightFun_antitone {d m : ℕ} {D : Finset (Fin (d + 1) → Fin m)}
    (hD : IsDownsetDim (d + 1) m D) : Antitone (heightFun d m D) := by
  intro f g hfg
  simp only [heightFun, Fin.le_def, Fin.val_mk]
  apply Finset.card_le_card
  intro k hk
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact hD _ hk _ ((extendByZ_preserves_le d m f g k).mp hfg)

/-! ## Round trip: D = subGraph(heightFun(D)) -/

/-- For a downset, fiber at f is an initial segment. -/
theorem downset_fiber_init {d m : ℕ} {D : Finset (Fin (d + 1) → Fin m)}
    (hD : IsDownsetDim (d + 1) m D) (f : Fin d → Fin m)
    {j : Fin m} (hj : j ∈ fiber d m D f) {i : Fin m} (hij : i ≤ j) :
    i ∈ fiber d m D f := by
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  apply hD _ hj
  -- extendByZ f i ≤ extendByZ f j
  intro ⟨idx, hidx⟩
  unfold extendByZ
  split_ifs with h
  · exact le_refl _
  · exact hij

theorem downset_eq_subGraph {d m : ℕ} {D : Finset (Fin (d + 1) → Fin m)}
    (hD : IsDownsetDim (d + 1) m D) :
    D = subGraph d m (heightFun d m D) := by
  ext p
  have hrecon : extendByZ d m
    (fun i : Fin d => p ⟨i.val, by omega⟩) (p ⟨d, by omega⟩) = p :=
    extendByZ_reconstruct d m p
  set f := fun i : Fin d => p ⟨i.val, by omega⟩
  set k := p ⟨d, by omega⟩
  rw [← hrecon, mem_subGraph_ext]
  simp only [heightFun, Fin.val_mk]
  constructor
  · intro hp
    have hk : k ∈ fiber d m D f := by
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp
    -- Initial segment: all j ≤ k are in fiber
    -- So |fiber| > k
    by_contra hle; push_neg at hle
    -- fiber ⊇ {j : j ≤ k}, so |fiber| ≥ k+1
    have : (Finset.Iic k) ⊆ fiber d m D f := by
      intro j hj; exact downset_fiber_init hD f hk (Finset.mem_Iic.mp hj)
    have := Finset.card_le_card this
    rw [Fin.card_Iic] at this
    omega
  · intro hp
    -- |fiber| > k, and fiber is initial segment, so k ∈ fiber
    by_contra hk_not
    -- All elements of fiber are < k (by initial segment + k ∉ fiber)
    have hlt : ∀ j ∈ fiber d m D f, j < k := by
      intro j hj
      by_contra hjk; push_neg at hjk
      have := downset_fiber_init hD f hj hjk
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact hk_not this
    -- So fiber ⊆ Iio k, and |Iio k| = k
    have hsub : fiber d m D f ⊆ Finset.Iio k := by
      intro j hj; exact Finset.mem_Iio.mpr (hlt j hj)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-! ## Main theorem -/

theorem downsetCountDim_eq_antitone_count (d m : ℕ) :
    downsetCountDim (d + 1) m =
    ((Finset.univ : Finset ((Fin d → Fin m) → Fin (m + 1))).filter Antitone).card := by
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn (heightFun d m)
    · intro D hD
      rw [Finset.mem_coe, Finset.mem_filter] at hD ⊢
      exact ⟨Finset.mem_univ _, heightFun_antitone hD.2⟩
    · intro D hD E hE heq
      rw [Finset.mem_coe, Finset.mem_filter] at hD hE
      rw [downset_eq_subGraph hD.2, downset_eq_subGraph hE.2, heq]
  · apply Finset.card_le_card_of_injOn (subGraph d m)
    · intro φ hφ
      rw [Finset.mem_coe, Finset.mem_filter] at hφ ⊢
      exact ⟨Finset.mem_powerset.mpr (fun _ _ => Finset.mem_univ _),
             subGraph_isDownset hφ.2⟩
    · intro φ _ ψ _ h; exact subGraph_injective d m h

end
end CausalAlgebraicGeometry.HeightBijection
