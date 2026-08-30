/-
  CAGNonproductScalingLimit.lean — Local continuum operators on arbitrary
  finite causal posets.

  The number of occupied events gives every downset state a canonical rank.
  For fields depending on this rank, the intrinsic causal-state Laplacian is
  proved exactly equal to a birth--death operator.  Its coefficients are the
  numbers of downward and upward neighboring states, so they are determined
  by causal branching rather than imposed externally.

  A fourth-order Taylor theorem then identifies the smooth local operator:
  branching imbalance produces drift, total branching produces diffusion,
  and imbalance also produces the leading skew correction.  The remainder
  is uniformly O(h²).  Balanced states recover a pure Laplacian, while a
  linear test field detects unbalanced singular drift exactly.

  This is the first continuum expansion in the repository that applies to
  arbitrary nonproduct finite causal posets.  It is radial in state rank; it
  is not yet a full tensorial limit on every state-space direction.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGSmoothScalingLimit
import Mathlib.Order.UpperLower.Closure

namespace CausalAlgebraicGeometry.CAGNonproductScalingLimit

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGFiniteCausalDynamics
open CausalAlgebraicGeometry.CAGProductScalingLimit
open CausalAlgebraicGeometry.CAGScalingLimit

noncomputable section
open scoped Classical

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Number of occupied causal events in a downset state. -/
def causalStateRank (s : LowerSet α) : ℕ :=
  (Finset.univ.filter fun a : α => a ∈ s).card

/-- Neighboring states reached by deleting one event. -/
def downwardNeighborFinset (s : LowerSet α) : Finset (LowerSet α) :=
  (lowerSetTransitionGraph (α := α)).neighborFinset s |>.filter fun t => t ≤ s

/-- Neighboring states reached by inserting one event.  The negated lower
comparison makes this the complementary partition of the neighbor set. -/
def upwardNeighborFinset (s : LowerSet α) : Finset (LowerSet α) :=
  (lowerSetTransitionGraph (α := α)).neighborFinset s |>.filter fun t => ¬t ≤ s

def downwardBranching (s : LowerSet α) : ℕ :=
  (downwardNeighborFinset s).card

def upwardBranching (s : LowerSet α) : ℕ :=
  (upwardNeighborFinset s).card

theorem rank_add_one_of_adj_of_le {s t : LowerSet α}
    (hadj : (lowerSetTransitionGraph (α := α)).Adj s t) (hst : s ≤ t) :
    causalStateRank t = causalStateRank s + 1 := by
  let S : Finset α := Finset.univ.filter fun a : α => a ∈ s
  let T : Finset α := Finset.univ.filter fun a : α => a ∈ t
  have hsub : S ⊆ T := by
    intro a ha
    have has : a ∈ s := by simpa [S] using ha
    simpa [T] using hst has
  have hfilter :
      (Finset.univ.filter fun a : α => (a ∈ s) ≠ (a ∈ t)) = T \ S := by
    ext a
    have himp : a ∈ s → a ∈ t := fun ha => hst ha
    by_cases has : a ∈ s <;> by_cases hat : a ∈ t <;>
      simp_all [S, T]
  have hdist : lowerSetDistance s t = 1 := hadj
  rw [lowerSetDistance_eq_card_filter, hfilter, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsub] at hdist
  have hcard : S.card ≤ T.card := Finset.card_le_card hsub
  change T.card = S.card + 1
  omega

theorem rank_sub_one_of_adj_of_le {s t : LowerSet α}
    (hadj : (lowerSetTransitionGraph (α := α)).Adj s t) (hts : t ≤ s) :
    causalStateRank t = causalStateRank s - 1 := by
  have h := rank_add_one_of_adj_of_le hadj.symm hts
  omega

theorem le_of_adj_of_not_le {s t : LowerSet α}
    (hadj : (lowerSetTransitionGraph (α := α)).Adj s t)
    (hnle : ¬t ≤ s) : s ≤ t := by
  rcases (lowerSetTransitionGraph_adj_iff_covBy s t).mp hadj with hst | hts
  · exact hst.le
  · exact False.elim (hnle hts.le)

/-- A scalar field depending only on the event-count rank. -/
def radialStateField (F : ℕ → ℝ) : LowerSet α → ℝ :=
  fun s => F (causalStateRank s)

/-- **EXACT NONPRODUCT RADIAL OPERATOR.** On every finite causal poset, the
state-graph Laplacian of a rank field is a birth-death operator whose two
coefficients are the downward and upward local branching numbers. -/
theorem causalStateLaplacian_radial_exact (F : ℕ → ℝ) (s : LowerSet α) :
    causalStateLaplacian (radialStateField F) s =
      downwardBranching s *
          (F (causalStateRank s) - F (causalStateRank s - 1)) +
        upwardBranching s *
          (F (causalStateRank s) - F (causalStateRank s + 1)) := by
  unfold causalStateLaplacian graphLaplacian
  rw [← Finset.sum_filter_add_sum_filter_not
    ((lowerSetTransitionGraph (α := α)).neighborFinset s) (fun t => t ≤ s)]
  change
    (∑ t ∈ downwardNeighborFinset s,
        (radialStateField F s - radialStateField F t)) +
      (∑ t ∈ upwardNeighborFinset s,
        (radialStateField F s - radialStateField F t)) = _
  have hdown :
      (∑ t ∈ downwardNeighborFinset s,
          (radialStateField F s - radialStateField F t)) =
        downwardBranching s *
          (F (causalStateRank s) - F (causalStateRank s - 1)) := by
    calc
      _ = ∑ _t ∈ downwardNeighborFinset s,
          (F (causalStateRank s) - F (causalStateRank s - 1)) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' := (Finset.mem_filter.mp ht)
        have hadj : (lowerSetTransitionGraph (α := α)).Adj s t := by
          simpa using ht'.1
        rw [radialStateField, radialStateField,
          rank_sub_one_of_adj_of_le hadj ht'.2]
      _ = _ := by
        simp [downwardBranching, Finset.sum_const, nsmul_eq_mul]
        ring
  have hup :
      (∑ t ∈ upwardNeighborFinset s,
          (radialStateField F s - radialStateField F t)) =
        upwardBranching s *
          (F (causalStateRank s) - F (causalStateRank s + 1)) := by
    calc
      _ = ∑ _t ∈ upwardNeighborFinset s,
          (F (causalStateRank s) - F (causalStateRank s + 1)) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' := (Finset.mem_filter.mp ht)
        have hadj : (lowerSetTransitionGraph (α := α)).Adj s t := by
          simpa using ht'.1
        have hst := le_of_adj_of_not_le hadj ht'.2
        rw [radialStateField, radialStateField,
          rank_add_one_of_adj_of_le hadj hst]
      _ = _ := by
        simp [upwardBranching, Finset.sum_const, nsmul_eq_mul]
        ring
  rw [hdown, hup]

/-! ## Smooth local drift--diffusion expansion -/

/-- Unequal downward and upward branching produces an asymmetric centered
difference. -/
def asymmetricRadialDifference (down up : ℝ) (f : ℝ → ℝ)
    (x h : ℝ) : ℝ :=
  (down * (f x - f (x - h)) + up * (f x - f (x + h))) / h ^ 2

/-- Third-order local differential operator selected by the two branching
numbers.  The first term is drift, the second diffusion, and the third is the
leading skew correction. -/
def radialDriftDiffusionApproximation (down up : ℝ) (f : ℝ → ℝ)
    (x h : ℝ) : ℝ :=
  (down - up) / h * iteratedDeriv 1 f x -
    (down + up) / 2 * iteratedDeriv 2 f x +
    (down - up) * h / 6 * iteratedDeriv 3 f x

/-- Sharp fourth-order Taylor control for an asymmetric causal branching
operator. -/
theorem asymmetricRadialDifference_smooth_error
    (down up : ℝ) (hdown : 0 ≤ down) (hup : 0 ≤ up)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (M x h : ℝ)
    (hM : ∀ y, |iteratedDeriv 4 f y| ≤ M) (hh : 0 < h) :
    |asymmetricRadialDifference down up f x h -
        radialDriftDiffusionApproximation down up f x h| ≤
      (down + up) * M * h ^ 2 / 24 := by
  let rplus := f (x + h) -
    (f x + iteratedDeriv 1 f x * h +
      iteratedDeriv 2 f x * h ^ 2 / 2 +
      iteratedDeriv 3 f x * h ^ 3 / 6)
  let rminus := f (x - h) -
    (f x - iteratedDeriv 1 f x * h +
      iteratedDeriv 2 f x * h ^ 2 / 2 -
      iteratedDeriv 3 f x * h ^ 3 / 6)
  have hp : |rplus| ≤ M * h ^ 4 / 24 :=
    taylorThird_remainder_bound_right f hf M x h hM hh
  have hm : |rminus| ≤ M * h ^ 4 / 24 :=
    taylorThird_remainder_bound_left f hf M x h hM hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  have herr :
      asymmetricRadialDifference down up f x h -
          radialDriftDiffusionApproximation down up f x h =
        -(down * rminus + up * rplus) / h ^ 2 := by
    dsimp [asymmetricRadialDifference, radialDriftDiffusionApproximation,
      rminus, rplus]
    field_simp [hh0]
    ring
  rw [herr, abs_div, abs_neg, abs_of_nonneg (sq_nonneg h)]
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  calc
    |down * rminus + up * rplus| ≤
        |down * rminus| + |up * rplus| := abs_add_le _ _
    _ = down * |rminus| + up * |rplus| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hdown, abs_of_nonneg hup]
    _ ≤ down * (M * h ^ 4 / 24) + up * (M * h ^ 4 / 24) :=
      add_le_add (mul_le_mul_of_nonneg_left hm hdown)
        (mul_le_mul_of_nonneg_left hp hup)
    _ = ((down + up) * M * h ^ 2 / 24) * h ^ 2 := by ring

/-- External rank coordinate with event spacing `h`. -/
def causalRankCoordinate (h : ℝ) (s : LowerSet α) : ℝ :=
  h * causalStateRank s

/-- Sample a continuum scalar field along causal-state rank. -/
def causalRankSample (h : ℝ) (f : ℝ → ℝ) : LowerSet α → ℝ :=
  fun s => f (causalRankCoordinate h s)

/-- Exact identification of the scaled nonproduct radial CAG operator with
the asymmetric difference selected by local branching. -/
theorem scaledCausalStateLaplacian_radial_exact
    (f : ℝ → ℝ) (s : LowerSet α) (h : ℝ)
    (hrank : 0 < causalStateRank s) :
    causalStateLaplacian (causalRankSample h f) s / h ^ 2 =
      asymmetricRadialDifference (downwardBranching s) (upwardBranching s)
        f (causalRankCoordinate h s) h := by
  have hrankle : 1 ≤ causalStateRank s := hrank
  rw [show causalRankSample h f =
      radialStateField (fun r => f (h * (r : ℝ))) by rfl,
    causalStateLaplacian_radial_exact]
  unfold asymmetricRadialDifference causalRankCoordinate
  rw [Nat.cast_sub hrankle, Nat.cast_add]
  norm_num
  ring_nf

/-- **NONPRODUCT SMOOTH CAG EXPANSION.** At every positive-rank state of
every finite causal poset, the scaled radial CAG Laplacian has an explicit
local drift--diffusion--skew expansion, with `O(h²)` remainder controlled by
the total branching. -/
theorem scaledCausalStateLaplacian_radial_smooth_error
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (M : ℝ)
    (hM : ∀ y, |iteratedDeriv 4 f y| ≤ M)
    (s : LowerSet α) (h : ℝ) (hh : 0 < h)
    (hrank : 0 < causalStateRank s) :
    |causalStateLaplacian (causalRankSample h f) s / h ^ 2 -
        radialDriftDiffusionApproximation
          (downwardBranching s) (upwardBranching s) f
          (causalRankCoordinate h s) h| ≤
      (downwardBranching s + upwardBranching s) * M * h ^ 2 / 24 := by
  rw [scaledCausalStateLaplacian_radial_exact f s h hrank]
  exact asymmetricRadialDifference_smooth_error
    (downwardBranching s) (upwardBranching s) (by positivity) (by positivity)
    f hf M (causalRankCoordinate h s) h hM hh

/-- At a locally balanced state, drift and skew cancel and the nonproduct
operator is a pure Laplacian with multiplicity equal to the branching. -/
theorem scaledCausalStateLaplacian_balanced_smooth_error
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (M : ℝ)
    (hM : ∀ y, |iteratedDeriv 4 f y| ≤ M)
    (s : LowerSet α) (h : ℝ) (hh : 0 < h)
    (hrank : 0 < causalStateRank s)
    (hbalanced : downwardBranching s = upwardBranching s) :
    |causalStateLaplacian (causalRankSample h f) s / h ^ 2 +
        downwardBranching s *
          iteratedDeriv 2 f (causalRankCoordinate h s)| ≤
      downwardBranching s * M * h ^ 2 / 12 := by
  have hmain := scaledCausalStateLaplacian_radial_smooth_error
    f hf M hM s h hh hrank
  rw [← hbalanced] at hmain
  unfold radialDriftDiffusionApproximation at hmain
  norm_num at hmain
  ring_nf at hmain ⊢
  exact hmain

/-- A linear test field detects the singular drift caused by branching
imbalance exactly. -/
theorem scaledCausalStateLaplacian_linear_exact
    (s : LowerSet α) (h : ℝ) (hh : h ≠ 0)
    (hrank : 0 < causalStateRank s) :
    causalStateLaplacian (causalRankSample h id) s / h ^ 2 =
      ((downwardBranching s : ℝ) - upwardBranching s) / h := by
  rw [scaledCausalStateLaplacian_radial_exact id s h hrank]
  unfold asymmetricRadialDifference causalRankCoordinate
  dsimp [id]
  field_simp [hh]
  ring

/-- A uniform bound on total branching converts the local `O(h²)` estimates
into an actual fixed-domain convergence theorem, even when the causal poset
and chosen state vary with `n`. -/
theorem boundedBranchingError_tendsto_zero
    (B M L : ℝ) (error : ℕ → ℝ)
    (hbound : ∀ n,
      |error n| ≤ B * M * (chainMesh L n) ^ 2 / 24) :
    Filter.Tendsto error Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun n => abs_nonneg (error n)) hbound
  have hcert := (smoothConsistencyError_tendsto_zero (B * M / 2)).comp
    (chainMesh_tendsto_zero L)
  convert hcert using 1
  funext n
  dsimp [Function.comp_def]
  ring

end
end CausalAlgebraicGeometry.CAGNonproductScalingLimit
