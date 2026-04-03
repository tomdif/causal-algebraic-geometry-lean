/-
  DownsetSymmetry.lean — The order-reversal bijection between downsets and upsets.

  KEY THEOREM: downsetCountDim d m = upsetCountDim d m

  Proof: The map f ↦ (fun i => rev(f i)) where rev(k) = m-1-k reverses
  the product order, sending downsets to upsets bijectively.

  COROLLARY: |CC([m]^d)| ≤ (downsetCountDim d m)²

  This tightens numConvexDim_le_exp from downsetCount × upsetCount to downsetCount².

  Zero sorry.
-/
import CausalAlgebraicGeometry.DimensionLaw

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.DownsetSymmetry

open CausalAlgebraicGeometry.DimensionLaw

noncomputable section

open scoped Classical

/-! ## The order-reversal map -/

/-- Reverse a coordinate: k ↦ m-1-k. -/
def revCoord (m : ℕ) (k : Fin m) : Fin m :=
  ⟨m - 1 - k.val, by omega⟩

theorem revCoord_involutive (m : ℕ) : Function.Involutive (revCoord m) := by
  intro k; ext; simp [revCoord]; omega

theorem revCoord_injective (m : ℕ) : Function.Injective (revCoord m) :=
  (revCoord_involutive m).injective

theorem revCoord_surjective (m : ℕ) : Function.Surjective (revCoord m) :=
  (revCoord_involutive m).surjective

theorem revCoord_antitone (m : ℕ) (a b : Fin m) (h : a ≤ b) :
    revCoord m b ≤ revCoord m a := by
  simp [revCoord, Fin.le_def]; omega

/-- Reverse all coordinates of a point in [m]^d. -/
def revPoint (d m : ℕ) (f : Fin d → Fin m) : Fin d → Fin m :=
  fun i => revCoord m (f i)

set_option maxRecDepth 1024 in
theorem revPoint_involutive (d m : ℕ) : Function.Involutive (revPoint d m) := by
  intro f; ext i; simp [revPoint, revCoord]; omega

theorem revPoint_injective (d m : ℕ) : Function.Injective (revPoint d m) :=
  (revPoint_involutive d m).injective

/-- revPoint reverses the product order: f ≤ g ↔ revPoint g ≤ revPoint f. -/
theorem revPoint_antitone (d m : ℕ) (f g : Fin d → Fin m) :
    f ≤ g ↔ revPoint d m g ≤ revPoint d m f := by
  constructor
  · intro h i; exact revCoord_antitone m _ _ (h i)
  · intro h i
    have hi := h i
    unfold revPoint revCoord at hi
    simp only [Fin.le_def, Fin.val_mk] at hi
    exact Fin.le_def.mpr (by omega)

/-! ## Mapping downsets to upsets -/

/-- Map a subset S to its pointwise reversal. -/
def revSet (d m : ℕ) (S : Finset (Fin d → Fin m)) : Finset (Fin d → Fin m) :=
  S.map ⟨revPoint d m, revPoint_injective d m⟩

theorem mem_revSet (d m : ℕ) (S : Finset (Fin d → Fin m)) (q : Fin d → Fin m) :
    q ∈ revSet d m S ↔ revPoint d m q ∈ S := by
  simp only [revSet, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rwa [revPoint_involutive d m]
  · intro h
    exact ⟨revPoint d m q, h, revPoint_involutive d m q⟩

theorem revSet_involutive (d m : ℕ) : Function.Involutive (revSet d m) := by
  intro S
  ext q
  rw [mem_revSet, mem_revSet, revPoint_involutive]

theorem revSet_injective (d m : ℕ) : Function.Injective (revSet d m) :=
  (revSet_involutive d m).injective

/-- Reversing a downset gives an upset. -/
theorem revSet_downset_is_upset {d m : ℕ} {D : Finset (Fin d → Fin m)}
    (hD : IsDownsetDim d m D) : IsUpsetDim d m (revSet d m D) := by
  intro p hp q hpq
  rw [mem_revSet] at hp ⊢
  apply hD _ hp
  exact (revPoint_antitone d m p q).mp hpq

/-- Reversing an upset gives a downset. -/
theorem revSet_upset_is_downset {d m : ℕ} {U : Finset (Fin d → Fin m)}
    (hU : IsUpsetDim d m U) : IsDownsetDim d m (revSet d m U) := by
  intro p hp q hqp
  rw [mem_revSet] at hp ⊢
  apply hU _ hp
  exact (revPoint_antitone d m q p).mp hqp

/-! ## The bijection between downsets and upsets -/

/-- revSet maps the set of downsets bijectively onto the set of upsets. -/
theorem revSet_maps_downsets_to_upsets (d m : ℕ) :
    ∀ S ∈ (Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsDownsetDim d m),
      revSet d m S ∈ (Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsUpsetDim d m) := by
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨Finset.mem_powerset.mpr (fun _ _ => Finset.mem_univ _),
         revSet_downset_is_upset hS.2⟩

/-- The main theorem: downsetCountDim = upsetCountDim. -/
theorem downsetCountDim_eq_upsetCountDim (d m : ℕ) :
    downsetCountDim d m = upsetCountDim d m := by
  unfold downsetCountDim upsetCountDim
  set DS := (Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsDownsetDim d m)
  set US := (Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsUpsetDim d m)
  -- revSet is an injection from DS to US
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn (revSet d m)
    · intro S hS
      exact Finset.mem_coe.mpr (revSet_maps_downsets_to_upsets d m S (Finset.mem_coe.mp hS))
    · intro S _ T _ h
      exact revSet_injective d m h
  · -- revSet is also an injection from US to DS (via revSet_upset_is_downset)
    apply Finset.card_le_card_of_injOn (revSet d m)
    · intro U hU
      rw [Finset.mem_coe] at hU ⊢
      rw [Finset.mem_filter] at hU ⊢
      exact ⟨Finset.mem_powerset.mpr (fun _ _ => Finset.mem_univ _),
             revSet_upset_is_downset hU.2⟩
    · intro S _ T _ h
      exact revSet_injective d m h

/-! ## Corollary: improved upper bound -/

/-- |CC([m]^d)| ≤ (downsetCountDim d m)². -/
theorem numConvexDim_le_downsetCount_sq (d m : ℕ) :
    numConvexDim d m ≤ downsetCountDim d m ^ 2 := by
  calc numConvexDim d m
      ≤ downsetCountDim d m * upsetCountDim d m := numConvexDim_le_exp d m
    _ = downsetCountDim d m * downsetCountDim d m := by
        rw [downsetCountDim_eq_upsetCountDim]
    _ = downsetCountDim d m ^ 2 := by ring

end -- noncomputable section

end CausalAlgebraicGeometry.DownsetSymmetry
