/-
  TightUpperBound.lean — numGridConvex m m ≤ C(2m,m)² ≤ 16^m

  Tightens the MonotoneProfileBound from 32^m to C(2m,m)² using the exact
  count of antitone functions from AntitoneCount.lean.

  Key result: numGridConvex_le_choose_sq, numGridConvex_le_sixteen_pow

  Zero sorry. Zero custom axioms.
-/
import CausalAlgebraicGeometry.MonotoneProfileBound
import CausalAlgebraicGeometry.AntitoneCount
import Mathlib.Data.Nat.Choose.Bounds

namespace CausalAlgebraicGeometry.TightUpperBound

open CausalAlgebraicGeometry.MonotoneProfileBound
open CausalAlgebraicGeometry.Supermultiplicativity
open CausalAlgebraicGeometry.GridClassification
open CausalAlgebraicGeometry.AntitoneCount

/-! ## Tight bound on downsets: exactly C(2m,m) -/

/-- The number of downsets of [m]² equals C(2m,m), since downsets biject with
    antitone boundary functions Fin m → Fin (m+1). -/
theorem card_downsets_eq_choose (m : ℕ) :
    ((Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m)).card =
      Nat.choose (2 * m) m := by
  -- Boundary map: D ↦ (fun i => |{j : (i,j) ∈ D}|)
  set bdy : Finset (Fin m × Fin m) → (Fin m → Fin (m + 1)) :=
    fun D i => ⟨((Finset.univ : Finset (Fin m)).filter (fun j => (i, j) ∈ D)).card,
      by have := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j => (i, j) ∈ D)
         simp [Finset.card_univ, Fintype.card_fin] at this; omega⟩ with bdy_def
  -- bdy maps downsets to antitone functions
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
  -- bdy is injective on downsets
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
-- Direction 1: |downsets| ≤ |antitone| via boundary map
  have h_le : ((Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m)).card ≤
      ((Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone).card :=
    Finset.card_le_card_of_injOn bdy
      (fun D hD => Finset.mem_coe.mpr (h_maps D hD))
      (fun D₁ hD₁ D₂ hD₂ heq =>
        h_inj D₁ (Finset.mem_coe.mp hD₁) D₂ (Finset.mem_coe.mp hD₂) heq)
  -- Direction 2: |antitone| ≤ |downsets| via downsetOfBdy
  have h_ge : ((Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone).card ≤
      ((Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsDownset m)).card :=
    Finset.card_le_card_of_injOn (downsetOfBdy m)
      (fun f hf => by
        have hf' := (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
           downsetOfBdy_isDownset hf'⟩))
      (fun f₁ _ f₂ _ heq => downsetOfBdy_injective m heq)
  have h_eq : ((Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone).card =
      Nat.choose (2 * m) m := by
    rw [card_antitone_eq_choose m m, show m + m = 2 * m from by omega]
  omega

/-- The number of upsets of [m]² is at most C(2m,m). -/
theorem card_upsets_le_choose (m : ℕ) :
    ((Finset.univ : Finset (Fin m × Fin m)).powerset.filter (IsUpset m)).card ≤
      Nat.choose (2 * m) m := by
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
    _ = Nat.choose (2 * m) m := card_downsets_eq_choose m

/-! ## Main tight bound -/

/-- numGridConvex m m ≤ C(2m,m)², the tight upper bound via downset × upset injection. -/
theorem numGridConvex_le_choose_sq (m : ℕ) :
    numGridConvex m m ≤ Nat.choose (2 * m) m ^ 2 := by
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
    _ ≤ Nat.choose (2 * m) m * Nat.choose (2 * m) m := by
        apply Nat.mul_le_mul
        · exact le_of_eq (card_downsets_eq_choose m)
        · exact card_upsets_le_choose m
    _ = Nat.choose (2 * m) m ^ 2 := by ring

/-- C(2m,m) ≤ 4^m, from the binomial sum. -/
theorem choose_central_le_four_pow (m : ℕ) : Nat.choose (2 * m) m ≤ 4 ^ m := by
  calc Nat.choose (2 * m) m ≤ 2 ^ (2 * m) := Nat.choose_le_two_pow (2 * m) m
    _ = (2 ^ 2) ^ m := by rw [pow_mul]
    _ = 4 ^ m := by norm_num

/-- numGridConvex m m ≤ 16^m, the tight exponential bound. -/
theorem numGridConvex_le_sixteen_pow (m : ℕ) : numGridConvex m m ≤ 16 ^ m := by
  calc numGridConvex m m
      ≤ Nat.choose (2 * m) m ^ 2 := numGridConvex_le_choose_sq m
    _ ≤ (4 ^ m) ^ 2 := Nat.pow_le_pow_left (choose_central_le_four_pow m) 2
    _ = 16 ^ m := by
        rw [← pow_mul, show m * 2 = 2 * m from by ring,
            show (4 : ℕ) ^ (2 * m) = (4 ^ 2) ^ m from pow_mul 4 2 m]; norm_num

end CausalAlgebraicGeometry.TightUpperBound
