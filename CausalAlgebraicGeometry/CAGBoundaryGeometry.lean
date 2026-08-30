/-
  CAGBoundaryGeometry.lean — Intrinsic geometry of CAG boundary profiles.

  The c₃ compression theorem identifies antitone boundary profiles as the
  macroscopic degrees of freedom of a causal-convex slab.  This file equips
  those profiles with two honest geometric structures:

  * `boundaryDistanceNat`: the L¹ height distance, proved to satisfy all metric
    axioms (with values in ℕ);
  * `plaquetteCurvatureOf`: the mixed second-difference tensor of the embedded
    height graph, proved symmetric in its coordinate indices and zero on
    constant fields.

  This is a state-space/discrete-surface geometry.  It is not asserted to be a
  Lorentzian spacetime metric or the Riemann tensor of general relativity.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.C3BarrierLowerBound
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.CAGBoundaryGeometry

open CausalAlgebraicGeometry.C3BarrierLowerBound

noncomputable section
open scoped Classical

/-! ## A genuine metric on boundary profiles -/

/-- L¹ distance between two integer height graphs.  It is intrinsic to the
profile representation and counts the number of vertical unit cells in their
symmetric difference. -/
def boundaryDistanceNat {d m : ℕ} (p q : AntitoneProfile d m) : ℕ :=
  ∑ f : Fin d → Fin m, Nat.dist (p.toFun f).val (q.toFun f).val

@[simp]
theorem boundaryDistanceNat_self {d m : ℕ} (p : AntitoneProfile d m) :
    boundaryDistanceNat p p = 0 := by
  simp [boundaryDistanceNat]

theorem boundaryDistanceNat_comm {d m : ℕ} (p q : AntitoneProfile d m) :
    boundaryDistanceNat p q = boundaryDistanceNat q p := by
  unfold boundaryDistanceNat
  apply Finset.sum_congr rfl
  intro f _
  exact Nat.dist_comm _ _

theorem boundaryDistanceNat_eq_zero_iff {d m : ℕ} (p q : AntitoneProfile d m) :
    boundaryDistanceNat p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hall : ∀ f : Fin d → Fin m,
        Nat.dist (p.toFun f).val (q.toFun f).val = 0 := by
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin d → Fin m)))
        (f := fun f => Nat.dist (p.toFun f).val (q.toFun f).val)
        (fun _ _ => Nat.zero_le _)).mp h
      intro f
      exact hs f (Finset.mem_univ f)
    apply AntitoneProfile.ext
    funext f
    apply Fin.ext
    exact Nat.eq_of_dist_eq_zero (hall f)
  · rintro rfl
    exact boundaryDistanceNat_self p

theorem boundaryDistanceNat_triangle {d m : ℕ}
    (p q r : AntitoneProfile d m) :
    boundaryDistanceNat p r ≤ boundaryDistanceNat p q + boundaryDistanceNat q r := by
  unfold boundaryDistanceNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f _
  exact Nat.dist.triangle_inequality _ _ _

/-- The metric axioms, packaged without imposing a global Mathlib metric-space
instance.  The distance has an exact combinatorial meaning as cell volume. -/
theorem boundaryDistanceNat_metric_axioms {d m : ℕ} :
    (∀ p : AntitoneProfile d m, boundaryDistanceNat p p = 0) ∧
    (∀ p q : AntitoneProfile d m,
      boundaryDistanceNat p q = 0 → p = q) ∧
    (∀ p q : AntitoneProfile d m,
      boundaryDistanceNat p q = boundaryDistanceNat q p) ∧
    (∀ p q r : AntitoneProfile d m,
      boundaryDistanceNat p r ≤ boundaryDistanceNat p q + boundaryDistanceNat q r) :=
  ⟨boundaryDistanceNat_self,
   fun p q => (boundaryDistanceNat_eq_zero_iff p q).mp,
   boundaryDistanceNat_comm,
   boundaryDistanceNat_triangle⟩

/-! ## Discrete mixed curvature of the height graph -/

/-- Embed the lower corner of a grid cell into the profile base. -/
def cellBasePoint {d m : ℕ} (x : Fin d → Fin (m - 1)) : Fin d → Fin m :=
  fun i => ⟨(x i).val, by have := (x i).isLt; omega⟩

/-- Advance one coordinate from the lower corner of a grid cell. -/
def cellStep {d m : ℕ} (x : Fin d → Fin (m - 1)) (i : Fin d) :
    Fin d → Fin m :=
  fun l => if h : l = i then ⟨(x l).val + 1, by have := (x l).isLt; omega⟩
    else ⟨(x l).val, by have := (x l).isLt; omega⟩

/-- Advance either of two coordinates.  For distinct indices this is the
opposite corner of the elementary coordinate plaquette. -/
def cellStepBoth {d m : ℕ} (x : Fin d → Fin (m - 1)) (i j : Fin d) :
    Fin d → Fin m :=
  fun l => if h : l = i ∨ l = j then
      ⟨(x l).val + 1, by have := (x l).isLt; omega⟩
    else ⟨(x l).val, by have := (x l).isLt; omega⟩

theorem cellStepBoth_comm {d m : ℕ} (x : Fin d → Fin (m - 1)) (i j : Fin d) :
    cellStepBoth x i j = cellStepBoth x j i := by
  funext l
  simp only [cellStepBoth]
  by_cases hli : l = i <;> by_cases hlj : l = j <;> simp [hli, hlj]

/-- Mixed second difference of an integer height field.  This is the discrete
Hessian/plaquette-curvature component Kᵢⱼ. -/
def plaquetteCurvatureOf {d m : ℕ} (h : (Fin d → Fin m) → ℤ)
    (x : Fin d → Fin (m - 1)) (i j : Fin d) : ℤ :=
  h (cellStepBoth x i j) - h (cellStep x i) - h (cellStep x j) + h (cellBasePoint x)

/-- Curvature tensor of an antitone CAG boundary surface. -/
def profileCurvature {d m : ℕ} (p : AntitoneProfile d m)
    (x : Fin d → Fin (m - 1)) (i j : Fin d) : ℤ :=
  plaquetteCurvatureOf (fun f => (p.toFun f).val) x i j

/-- The mixed curvature tensor is symmetric. -/
theorem plaquetteCurvatureOf_symm {d m : ℕ} (h : (Fin d → Fin m) → ℤ)
    (x : Fin d → Fin (m - 1)) (i j : Fin d) :
    plaquetteCurvatureOf h x i j = plaquetteCurvatureOf h x j i := by
  unfold plaquetteCurvatureOf
  rw [cellStepBoth_comm x i j]
  ring

theorem profileCurvature_symm {d m : ℕ} (p : AntitoneProfile d m)
    (x : Fin d → Fin (m - 1)) (i j : Fin d) :
    profileCurvature p x i j = profileCurvature p x j i :=
  plaquetteCurvatureOf_symm _ _ _ _

/-- Constant height fields have zero mixed curvature. -/
@[simp]
theorem plaquetteCurvatureOf_const {d m : ℕ} (c : ℤ)
    (x : Fin d → Fin (m - 1)) (i j : Fin d) :
    plaquetteCurvatureOf (fun _ => c) x i j = 0 := by
  unfold plaquetteCurvatureOf
  ring

/-- Pointwise definition of a flat CAG boundary. -/
def IsPlaquetteFlat {d m : ℕ} (p : AntitoneProfile d m) : Prop :=
  ∀ x : Fin d → Fin (m - 1), ∀ i j : Fin d, i ≠ j →
    profileCurvature p x i j = 0

end
end CausalAlgebraicGeometry.CAGBoundaryGeometry
