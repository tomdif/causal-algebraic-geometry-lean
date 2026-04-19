/-
  FiberCardinality.lean — |fiber(f)| = upperBdy(f) - lowerBdy(f).

  CORE LEMMA: For convex S and nonempty fiber at f, the fiber has card
  exactly upperBdy(f) - lowerBdy(f).

  This is the key step for connecting convex-subset cardinality to
  antitone-pair sums via Σ_f |fiber(f)|.

  Zero sorry.
-/
import CausalAlgebraicGeometry.SlabCharacterization

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.FiberCardinality

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.SlicingBound
open CausalAlgebraicGeometry.SlabCharacterization

noncomputable section
open scoped Classical

/-! ## Fiber card via boundary difference -/

/-- For convex S with nonempty fiber at f, fiber card = upperBdy - lowerBdy.

    Proof: fiber_eq_Icc says fiber = {k : lowerBdy ≤ k.val < upperBdy}.
    We construct a bijection between this and Finset.Ico lowerBdy upperBdy,
    which has card upperBdy - lowerBdy. -/
theorem fiber_card_eq_diff {d m : ℕ}
    {S : Finset (Fin (d + 1) → Fin m)}
    (hS : IsConvexDim (d + 1) m S)
    (f : Fin d → Fin m)
    (hne : (fiber d m S f).Nonempty) :
    (fiber d m S f).card = upperBdy d m S f - lowerBdy d m S f := by
  -- Rewrite fiber using fiber_eq_Icc.
  have h_eq : fiber d m S f = (Finset.univ : Finset (Fin m)).filter
      (fun k => lowerBdy d m S f ≤ k.val ∧ k.val < upperBdy d m S f) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fiber_eq_Icc hS f k
  rw [h_eq]
  -- Bounds: lowerBdy < m and upperBdy ≤ m.
  have hlb_lt_m : lowerBdy d m S f < m := by
    unfold lowerBdy; rw [dif_pos hne]
    exact ((fiber d m S f).min' hne).isLt
  have hub_le_m : upperBdy d m S f ≤ m := by
    unfold upperBdy; rw [dif_pos hne]
    have := ((fiber d m S f).max' hne).isLt
    omega
  -- Construct bijection Ico lowerBdy upperBdy ↔ filtered Fin m.
  -- Bijection to Ico via embedding
  have : (Finset.univ : Finset (Fin m)).filter
          (fun k => lowerBdy d m S f ≤ k.val ∧ k.val < upperBdy d m S f) =
         (Finset.Ico (lowerBdy d m S f) (upperBdy d m S f)).attach.image
            (fun n => (⟨n.val, by
              have h := n.property
              rw [Finset.mem_Ico] at h
              omega⟩ : Fin m)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Finset.mem_attach, Finset.mem_Ico]
    constructor
    · rintro ⟨hlo, hhi⟩
      have hmem : k.val ∈ Finset.Ico (lowerBdy d m S f) (upperBdy d m S f) := by
        rw [Finset.mem_Ico]; exact ⟨hlo, hhi⟩
      refine ⟨⟨k.val, hmem⟩, ?_⟩
      exact Fin.ext rfl
    · rintro ⟨⟨n, hn⟩, rfl⟩
      rw [Finset.mem_Ico] at hn
      exact hn
  rw [this]
  rw [Finset.card_image_of_injective _ (by
    intro a b hab
    apply Subtype.ext
    exact Fin.val_eq_of_eq hab)]
  rw [Finset.card_attach, Nat.card_Ico]

/-- For empty fiber, card is 0. -/
theorem fiber_card_eq_zero_of_empty {d m : ℕ} (S : Finset (Fin (d + 1) → Fin m))
    (f : Fin d → Fin m) (he : ¬ (fiber d m S f).Nonempty) :
    (fiber d m S f).card = 0 := by
  rw [Finset.not_nonempty_iff_eq_empty] at he
  rw [he, Finset.card_empty]

/-- For empty fiber, upperBdy - lowerBdy = 0 (in ℕ subtraction, since lowerBdy = m, upperBdy = 0). -/
theorem bdy_diff_eq_zero_of_empty {d m : ℕ} (S : Finset (Fin (d + 1) → Fin m))
    (f : Fin d → Fin m) (he : ¬ (fiber d m S f).Nonempty) :
    upperBdy d m S f - lowerBdy d m S f = 0 := by
  unfold upperBdy lowerBdy
  rw [dif_neg he, dif_neg he]
  omega

/-- Unified: |fiber(f)| = upperBdy(f) - lowerBdy(f) always (using ℕ truncated subtraction
    and the canonical empty convention lowerBdy = m, upperBdy = 0). -/
theorem fiber_card_eq_bdy_diff {d m : ℕ}
    {S : Finset (Fin (d + 1) → Fin m)}
    (hS : IsConvexDim (d + 1) m S)
    (f : Fin d → Fin m) :
    (fiber d m S f).card = upperBdy d m S f - lowerBdy d m S f := by
  by_cases hne : (fiber d m S f).Nonempty
  · exact fiber_card_eq_diff hS f hne
  · rw [fiber_card_eq_zero_of_empty S f hne, bdy_diff_eq_zero_of_empty S f hne]

/-! ## The fibration cardinality identity -/

/-- Extract the base coordinates of a point in [m]^{d+1}. -/
def baseOf (d m : ℕ) (p : Fin (d + 1) → Fin m) : Fin d → Fin m :=
  fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- For any S ⊆ [m]^{d+1}, filtering by base = f is in bijection with the fiber. -/
theorem filter_base_card_eq_fiber_card {d m : ℕ}
    (S : Finset (Fin (d + 1) → Fin m)) (f : Fin d → Fin m) :
    (S.filter (fun p => baseOf d m p = f)).card = (fiber d m S f).card := by
  -- Bijection: p ↔ lastOf p (and inverse: y ↦ extendByZ f y).
  apply Finset.card_bij (fun p _ => p ⟨d, Nat.lt_succ_self d⟩)
  · -- Map from filter to fiber
    intro p hp
    rw [Finset.mem_filter] at hp
    unfold fiber
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- Need extendByZ d m f (p ⟨d, _⟩) ∈ S
    have : extendByZ d m f (p ⟨d, Nat.lt_succ_self d⟩) = p := by
      have := hp.2  -- baseOf p = f
      rw [← this]
      exact extendByZ_reconstruct d m p
    rw [this]; exact hp.1
  · -- Injectivity
    intro p₁ hp₁ p₂ hp₂ h
    rw [Finset.mem_filter] at hp₁ hp₂
    -- p₁ and p₂ both have baseOf = f; both lastOf agree.
    -- So p₁ = p₂ by reconstruction.
    have h1 : extendByZ d m f (p₁ ⟨d, Nat.lt_succ_self d⟩) = p₁ := by
      rw [← hp₁.2]; exact extendByZ_reconstruct d m p₁
    have h2 : extendByZ d m f (p₂ ⟨d, Nat.lt_succ_self d⟩) = p₂ := by
      rw [← hp₂.2]; exact extendByZ_reconstruct d m p₂
    rw [← h1, ← h2, h]
  · -- Surjectivity
    intro y hy
    unfold fiber at hy
    rw [Finset.mem_filter] at hy
    refine ⟨extendByZ d m f y, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨hy.2, ?_⟩
      unfold baseOf
      funext i
      exact extendByZ_init d m f y i
    · exact extendByZ_last d m f y

/-- **THE FIBRATION IDENTITY**: |S| = Σ_f |fiber_S(f)| for any S ⊆ [m]^{d+1}.

    Proof: partition S by the base-coordinate map, and use that each fiber
    bijects with the filter "S restricted to base = f". -/
theorem card_eq_sum_fiber_card {d m : ℕ} (S : Finset (Fin (d + 1) → Fin m)) :
    S.card = (Finset.univ : Finset (Fin d → Fin m)).sum (fun f => (fiber d m S f).card) := by
  -- Use Finset.card_eq_sum_card_fiberwise which says
  -- sum over t of |{x ∈ s : f x = b}| = |s| when f maps into t.
  have := Finset.card_eq_sum_card_fiberwise (f := baseOf d m) (s := S) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)
  rw [this]
  apply Finset.sum_congr rfl
  intro f _
  exact filter_base_card_eq_fiber_card S f

/-! ## Defect formula -/

/-- For convex S with all fibers nonempty (near-vacuum regime),
    |S^c| = Σ_f (m - upperBdy(f) + lowerBdy(f)). -/
theorem defect_eq_sum_bdy {d m : ℕ}
    {S : Finset (Fin (d + 1) → Fin m)}
    (hS : IsConvexDim (d + 1) m S)
    (hne : ∀ f : Fin d → Fin m, (fiber d m S f).Nonempty) :
    (Finset.univ \ S).card =
    (Finset.univ : Finset (Fin d → Fin m)).sum
      (fun f => m - upperBdy d m S f + lowerBdy d m S f) := by
  -- |univ \ S| = |univ| - |S|
  have h_sdiff : (Finset.univ \ S).card =
      (Finset.univ : Finset (Fin (d + 1) → Fin m)).card - S.card := by
    rw [Finset.card_sdiff]
    · congr 1
      rw [Finset.inter_eq_left.mpr (Finset.subset_univ S)]
    -- Removed second hypothesis; try inferring otherwise
  rw [h_sdiff]
  -- |univ| = m^{d+1} = sum over f of m
  have h_univ_card : (Finset.univ : Finset (Fin (d + 1) → Fin m)).card =
      (Finset.univ : Finset (Fin d → Fin m)).sum (fun _ => m) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    simp [Fintype.card_fun, Fintype.card_fin]
    ring
  rw [h_univ_card, card_eq_sum_fiber_card S]
  -- Now: Σ m - Σ |fiber(f)| = Σ (m - |fiber(f)|) = Σ (m - (upperBdy - lowerBdy))
  rw [← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl
    intro f _
    rw [fiber_card_eq_diff hS f (hne f)]
    have hlb : lowerBdy d m S f < m := by
      unfold lowerBdy; rw [dif_pos (hne f)]
      exact ((fiber d m S f).min' (hne f)).isLt
    have hub_le_m : upperBdy d m S f ≤ m := by
      unfold upperBdy; rw [dif_pos (hne f)]
      have := ((fiber d m S f).max' (hne f)).isLt
      omega
    have hub_ge_lb : lowerBdy d m S f < upperBdy d m S f := by
      unfold lowerBdy upperBdy; rw [dif_pos (hne f), dif_pos (hne f)]
      have := Finset.min'_le _ _ (Finset.max'_mem (fiber d m S f) (hne f))
      have h := Fin.le_def.mp this
      omega
    omega
  · intro f _
    rw [fiber_card_eq_diff hS f (hne f)]
    have hub_le_m : upperBdy d m S f ≤ m := by
      unfold upperBdy; rw [dif_pos (hne f)]
      have := ((fiber d m S f).max' (hne f)).isLt
      omega
    omega

/-! ## Summary

PROVED (zero sorry):

1. fiber_card_eq_diff: for convex S with nonempty fiber at f,
   |fiber_S(f)| = upperBdy_S(f) - lowerBdy_S(f).

2. fiber_card_eq_zero_of_empty: empty fiber has card 0.

3. bdy_diff_eq_zero_of_empty: when fiber empty, upperBdy - lowerBdy = 0
   (under ℕ truncated subtraction with lowerBdy = m > upperBdy = 0).

4. fiber_card_eq_bdy_diff: unified statement without nonempty hypothesis.

CONSEQUENCE:
  For any convex S ⊆ [m]^{d+1}, the sum of fiber cards over [m]^d gives |S|:
    |S| = Σ_f |fiber_S(f)| = Σ_f (upperBdy_S(f) - lowerBdy_S(f))

  The first equality (|S| = Σ_f |fiber(f)|) is the fibration identity, which
  holds by partitioning [m]^{d+1} via the (base, last) decomposition. This
  file provides the per-fiber identity; the fibration sum identity is a
  standard counting argument using Finset.sum_fintype that we don't formalize
  separately here.

  Combining: |S^c| = m^{d+1} - |S| = Σ_f (m - upperBdy(f) + lowerBdy(f))
  when all fibers are nonempty (so lowerBdy ≤ upperBdy pointwise and no
  truncated-subtraction issues).

  This completes the per-fiber piece of the convex-subset cardinality
  decomposition needed for the near-vacuum theorem.
-/

end -- noncomputable section

end CausalAlgebraicGeometry.FiberCardinality
