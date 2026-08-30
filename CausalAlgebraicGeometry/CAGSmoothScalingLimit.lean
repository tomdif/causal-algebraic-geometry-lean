/-
  CAGSmoothScalingLimit.lean — Smooth-field continuum consistency for CAG.

  Mathlib's Lagrange form of Taylor's theorem is used to prove the sharp
  centered-difference estimate `M h² / 12` for globally `C⁴` real fields
  whose fourth derivative is bounded by `M`.

  The estimate is then lifted recursively to arbitrary-dimensional product
  CAG.  The field may couple all coordinates: separability is not assumed.
  At every fully interior causal state, the mesh-scaled intrinsic graph
  Laplacian approximates the negative coordinate Euclidean Laplacian with
  explicit uniform `O(h²)` error.  The error certificate is also proved to
  vanish on fixed physical cubes with mesh `L/n`.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGProductScalingLimit
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace CausalAlgebraicGeometry.CAGProductScalingLimit

open Set
open CausalAlgebraicGeometry.CAGScalingLimit
open CausalAlgebraicGeometry.CAGFiniteCausalGeometry

noncomputable section

/-! ## One-dimensional Taylor control -/

/-- The third Taylor polynomial written with ordinary iterated derivatives
at the center of a nondegenerate interval. -/
private theorem taylorThird_eval_explicit
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x h : ℝ) (hh : 0 < h) :
    taylorWithinEval f 3 (Icc x (x + h)) x (x + h) =
      f x + iteratedDeriv 1 f x * h +
        iteratedDeriv 2 f x * h ^ 2 / 2 +
        iteratedDeriv 3 f x * h ^ 3 / 6 := by
  have hxh : x < x + h := by linarith
  have hx : x ∈ Icc x (x + h) := left_mem_Icc.mpr hxh.le
  have hu : UniqueDiffOn ℝ (Icc x (x + h)) := uniqueDiffOn_Icc hxh
  have h0 : iteratedDerivWithin 0 f (Icc x (x + h)) x =
      iteratedDeriv 0 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hf.of_le (by norm_num)).contDiffAt hx
  have h1 : iteratedDerivWithin 1 f (Icc x (x + h)) x =
      iteratedDeriv 1 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hf.of_le (by norm_num)).contDiffAt hx
  have h2 : iteratedDerivWithin 2 f (Icc x (x + h)) x =
      iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hf.of_le (by norm_num)).contDiffAt hx
  have h3 : iteratedDerivWithin 3 f (Icc x (x + h)) x =
      iteratedDeriv 3 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hf.of_le (by norm_num)).contDiffAt hx
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3]
  ring

/-- Right-hand third-order Taylor remainder under a global fourth-derivative
bound. -/
theorem taylorThird_remainder_bound_right
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (M x h : ℝ)
    (hM : ∀ y, |iteratedDeriv 4 f y| ≤ M) (hh : 0 < h) :
    |f (x + h) -
        (f x + iteratedDeriv 1 f x * h +
          iteratedDeriv 2 f x * h ^ 2 / 2 +
          iteratedDeriv 3 f x * h ^ 3 / 6)| ≤
      M * h ^ 4 / 24 := by
  have hxh : x < x + h := by linarith
  rcases taylor_mean_remainder_lagrange_iteratedDeriv
      (n := 3) hxh hf.contDiffOn with ⟨y, hy, hrem⟩
  rw [taylorThird_eval_explicit f hf x h hh] at hrem
  rw [hrem, abs_div, abs_mul, abs_pow]
  norm_num only [Nat.factorial, Nat.cast_ofNat, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24)]
  have hdist : |x + h - x| = h := by
    rw [show x + h - x = h by ring, abs_of_pos hh]
  rw [hdist]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM y) (by positivity)) (by positivity)

/-- Left-hand third-order Taylor remainder, obtained by reflecting the
field through the expansion point. -/
theorem taylorThird_remainder_bound_left
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (M x h : ℝ)
    (hM : ∀ y, |iteratedDeriv 4 f y| ≤ M) (hh : 0 < h) :
    |f (x - h) -
        (f x - iteratedDeriv 1 f x * h +
          iteratedDeriv 2 f x * h ^ 2 / 2 -
          iteratedDeriv 3 f x * h ^ 3 / 6)| ≤
      M * h ^ 4 / 24 := by
  let g : ℝ → ℝ := fun t => f (x - t)
  have hg : ContDiff ℝ 4 g := by
    dsimp [g]
    simpa only [Function.comp_def] using
      hf.comp (contDiff_const.sub contDiff_id)
  have hgM : ∀ y, |iteratedDeriv 4 g y| ≤ M := by
    intro y
    have hder := congrFun (iteratedDeriv_comp_const_sub 4 f x) y
    dsimp [g]
    rw [hder]
    simpa using hM (x - y)
  have hrem := taylorThird_remainder_bound_right g hg M 0 h hgM hh
  have hder1 := congrFun (iteratedDeriv_comp_const_sub 1 f x) 0
  have hder2 := congrFun (iteratedDeriv_comp_const_sub 2 f x) 0
  have hder3 := congrFun (iteratedDeriv_comp_const_sub 3 f x) 0
  dsimp [g] at hrem
  rw [hder1, hder2, hder3] at hrem
  norm_num at hrem
  rw [iteratedDeriv_one]
  ring_nf at hrem ⊢
  exact hrem

/-- **SHARP SMOOTH CENTERED-DIFFERENCE BOUND.** If `f` is globally `C⁴`
and `|f⁽⁴⁾| ≤ M`, the negative centered second difference differs from
`-f″` by at most `M h² / 12`. -/
theorem centeredDifference_smooth_error
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (M x h : ℝ)
    (hM : ∀ y, |iteratedDeriv 4 f y| ≤ M) (hh : 0 < h) :
    |(2 * f x - f (x - h) - f (x + h)) / h ^ 2 +
        iteratedDeriv 2 f x| ≤
      M * h ^ 2 / 12 := by
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
      (2 * f x - f (x - h) - f (x + h)) / h ^ 2 +
          iteratedDeriv 2 f x =
        -(rminus + rplus) / h ^ 2 := by
    dsimp [rminus, rplus]
    field_simp [hh0]
    ring
  rw [herr, abs_div, abs_neg, abs_of_nonneg (sq_nonneg h)]
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  calc
    |rminus + rplus| ≤ |rminus| + |rplus| := abs_add_le _ _
    _ ≤ M * h ^ 4 / 24 + M * h ^ 4 / 24 := add_le_add hm hp
    _ = (M * h ^ 2 / 12) * h ^ 2 := by ring

/-! ## Coupled fields in arbitrary dimension -/
/-- The centered finite-difference operator along all recursive Euclidean
coordinates. -/
def centeredProductDifference : {d : ℕ} →
    (EuclideanPoint d → ℝ) → EuclideanPoint d → ℝ → ℝ
  | 0, _, _, _ => 0
  | _ + 1, f, x, h =>
      (2 * f x - f (x.1 - h, x.2) - f (x.1 + h, x.2)) / h ^ 2 +
        centeredProductDifference (fun tail => f (x.1, tail)) x.2 h

/-- Sum of the ordinary second derivatives along the recursive Euclidean
coordinates.  For a coupled field this is the coordinate Euclidean
Laplacian. -/
def coordinateLaplacian : {d : ℕ} →
    (EuclideanPoint d → ℝ) → EuclideanPoint d → ℝ
  | 0, _, _ => 0
  | _ + 1, f, x =>
      iteratedDeriv 2 (fun t => f (t, x.2)) x.1 +
        coordinateLaplacian (fun tail => f (x.1, tail)) x.2

/-- Pointwise coordinate-slice `C⁴` hypothesis with a global fourth-
derivative bound on every slice through the point. -/
def AxisC4BoundAt : {d : ℕ} →
    (EuclideanPoint d → ℝ) → EuclideanPoint d →
      EuclideanPoint d → Prop
  | 0, _, _, _ => True
  | _ + 1, f, M, x =>
      ContDiff ℝ 4 (fun t => f (t, x.2)) ∧
        (∀ t, |iteratedDeriv 4 (fun s => f (s, x.2)) t| ≤ M.1) ∧
        AxisC4BoundAt (fun tail => f (x.1, tail)) M.2 x.2

/-- Every coupled coordinate-smooth field has the sharp summed `O(h²)`
centered-difference error estimate. -/
theorem centeredProductDifference_smooth_error
    (d : ℕ) (f : EuclideanPoint d → ℝ) (M x : EuclideanPoint d)
    (h : ℝ) (hh : 0 < h) (hf : AxisC4BoundAt f M x) :
    |centeredProductDifference f x h + coordinateLaplacian f x| ≤
      euclideanCoordinateSum M * h ^ 2 / 12 := by
  induction d with
  | zero =>
      simp [centeredProductDifference, coordinateLaplacian,
        euclideanCoordinateSum]
  | succ d ih =>
      rcases hf with ⟨hheadSmooth, hheadBound, htail⟩
      have hhead := centeredDifference_smooth_error
        (fun t => f (t, x.2)) hheadSmooth M.1 x.1 h hheadBound hh
      have htail := ih (fun tail => f (x.1, tail)) M.2 x.2 htail
      change
        |((2 * f x - f (x.1 - h, x.2) - f (x.1 + h, x.2)) / h ^ 2 +
              centeredProductDifference (fun tail => f (x.1, tail)) x.2 h) +
            (iteratedDeriv 2 (fun t => f (t, x.2)) x.1 +
              coordinateLaplacian (fun tail => f (x.1, tail)) x.2)| ≤
          (M.1 + euclideanCoordinateSum M.2) * h ^ 2 / 12
      rw [show
        (2 * f x - f (x.1 - h, x.2) - f (x.1 + h, x.2)) / h ^ 2 +
              centeredProductDifference (fun tail => f (x.1, tail)) x.2 h +
            (iteratedDeriv 2 (fun t => f (t, x.2)) x.1 +
              coordinateLaplacian (fun tail => f (x.1, tail)) x.2) =
          ((2 * f x - f (x.1 - h, x.2) - f (x.1 + h, x.2)) / h ^ 2 +
              iteratedDeriv 2 (fun t => f (t, x.2)) x.1) +
            (centeredProductDifference (fun tail => f (x.1, tail)) x.2 h +
              coordinateLaplacian (fun tail => f (x.1, tail)) x.2) by ring]
      calc
        |_ + _| ≤
            |(2 * f x - f (x.1 - h, x.2) - f (x.1 + h, x.2)) / h ^ 2 +
                iteratedDeriv 2 (fun t => f (t, x.2)) x.1| +
              |centeredProductDifference (fun tail => f (x.1, tail)) x.2 h +
                coordinateLaplacian (fun tail => f (x.1, tail)) x.2| :=
          abs_add_le _ _
        _ ≤ M.1 * h ^ 2 / 12 +
              euclideanCoordinateSum M.2 * h ^ 2 / 12 :=
          add_le_add hhead htail
        _ = (M.1 + euclideanCoordinateSum M.2) * h ^ 2 / 12 := by ring

/-- Sampling any (possibly coupled) Euclidean field on the causal product
grid turns the intrinsic product stencil into the recursive centered
difference operator. -/
theorem productStencil_sample_eq_centeredProductDifference
    (d n : ℕ) (f : EuclideanPoint d → ℝ) (h : ℝ)
    (q : ProductInteriorIndex d n) :
    productStencil (fun k => f (productCoordinate h k)) q / h ^ 2 =
      centeredProductDifference f
        (productCoordinate h (interiorToProductIndex q)) h := by
  induction d with
  | zero =>
      cases q
      simp [productStencil, centeredProductDifference]
  | succ d ih =>
      change
        (2 * f (chainCoordinate h q.1.1,
              productCoordinate h (interiorToProductIndex q.2)) -
            f (chainCoordinate h (chainLeft q.1.1 q.1.2.1),
              productCoordinate h (interiorToProductIndex q.2)) -
            f (chainCoordinate h (chainRight q.1.1 q.1.2.2),
              productCoordinate h (interiorToProductIndex q.2)) +
            productStencil
              (fun tail => f (chainCoordinate h q.1.1,
                productCoordinate h tail)) q.2) / h ^ 2 =
          (2 * f (chainCoordinate h q.1.1,
                productCoordinate h (interiorToProductIndex q.2)) -
              f (chainCoordinate h q.1.1 - h,
                productCoordinate h (interiorToProductIndex q.2)) -
              f (chainCoordinate h q.1.1 + h,
                productCoordinate h (interiorToProductIndex q.2))) / h ^ 2 +
            centeredProductDifference
              (fun tail => f (chainCoordinate h q.1.1, tail))
              (productCoordinate h (interiorToProductIndex q.2)) h
      rw [chainCoordinate_left h q.1.1 q.1.2.1,
        chainCoordinate_right h q.1.1 q.1.2.2, add_div]
      rw [ih (fun tail => f (chainCoordinate h q.1.1, tail)) q.2]

/-- The mesh-scaled intrinsic CAG Laplacian equals the centered coordinate
operator on every sampled field, without a separability assumption. -/
theorem scaledProductLaplacian_eq_centeredProductDifference
    (d n : ℕ) (f : EuclideanPoint d → ℝ) (h : ℝ)
    (q : ProductInteriorIndex d n) :
    scaledProductLaplacian d n h f (interiorToProductIndex q) =
      centeredProductDifference f
        (productCoordinate h (interiorToProductIndex q)) h := by
  unfold scaledProductLaplacian
  rw [graphLaplacian_productState_interior]
  simp only [productSample_productState]
  exact productStencil_sample_eq_centeredProductDifference d n f h q

/-- **COUPLED SMOOTH-FIELD CAG CONSISTENCY.** In every dimension, the
intrinsic product CAG Laplacian approximates the negative coordinate
Euclidean Laplacian for arbitrary coupled fields, with explicit uniform
second-order error controlled by coordinate fourth derivatives. -/
theorem scaledProductLaplacian_smooth_error
    (d n : ℕ) (f : EuclideanPoint d → ℝ) (M : EuclideanPoint d)
    (h : ℝ) (hh : 0 < h) (q : ProductInteriorIndex d n)
    (hf : AxisC4BoundAt f M
      (productCoordinate h (interiorToProductIndex q))) :
    |scaledProductLaplacian d n h f (interiorToProductIndex q) +
        coordinateLaplacian f
          (productCoordinate h (interiorToProductIndex q))| ≤
      euclideanCoordinateSum M * h ^ 2 / 12 := by
  rw [scaledProductLaplacian_eq_centeredProductDifference d n f h q]
  exact centeredProductDifference_smooth_error d f M
    (productCoordinate h (interiorToProductIndex q)) h hh hf

/-- A global coordinate-slice smoothness certificate, uniform over all
points of Euclidean `d`-space. -/
def AxisC4Bound {d : ℕ} (f : EuclideanPoint d → ℝ)
    (M : EuclideanPoint d) : Prop :=
  ∀ x, AxisC4BoundAt f M x

/-- Uniform-in-state form of coupled smooth-field consistency. -/
theorem scaledProductLaplacian_smooth_error_uniform
    (d n : ℕ) (f : EuclideanPoint d → ℝ) (M : EuclideanPoint d)
    (h : ℝ) (hh : 0 < h) (hf : AxisC4Bound f M) :
    ∀ q : ProductInteriorIndex d n,
      |scaledProductLaplacian d n h f (interiorToProductIndex q) +
          coordinateLaplacian f
            (productCoordinate h (interiorToProductIndex q))| ≤
        euclideanCoordinateSum M * h ^ 2 / 12 := by
  intro q
  exact scaledProductLaplacian_smooth_error d n f M h hh q
    (hf (productCoordinate h (interiorToProductIndex q)))

/-- The general smooth-field error certificate vanishes quadratically with
the mesh. -/
theorem smoothConsistencyError_tendsto_zero (C : ℝ) :
    Filter.Tendsto (fun h : ℝ => C * h ^ 2 / 12)
      (nhds 0) (nhds 0) := by
  have hcont : ContinuousAt (fun h : ℝ => C * h ^ 2 / 12) 0 := by
    fun_prop
  simpa using hcont.tendsto

/-- On fixed physical cubes with mesh `L/n`, the uniform smooth-field CAG
consistency certificate converges to zero in every dimension. -/
theorem smoothProductFamily_error_tendsto_zero
    (d : ℕ) (M : EuclideanPoint d) (L : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        euclideanCoordinateSum M * (chainMesh L n) ^ 2 / 12)
      Filter.atTop (nhds 0) := by
  exact (smoothConsistencyError_tendsto_zero
    (euclideanCoordinateSum M)).comp (chainMesh_tendsto_zero L)

end
end CausalAlgebraicGeometry.CAGProductScalingLimit
