/-
  CSpecRingSheaf.lean — The causal-corner sheaf valued in noncommutative rings.

  `CSpecActualSheaf` supplies the topology and a sheaf of underlying types.
  Here we bundle each finite causal corner as a unital ring and prove that
  restriction of pointwise sections is a ring homomorphism.  The result is an
  actual `TopCat.Sheaf RingCat` whose underlying sheaf of types is the earlier
  construction.
-/
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Sheaves.SheafOfFunctions
import CausalAlgebraicGeometry.CSpecActualSheaf

namespace CausalAlgebraicGeometry.CSpecRingSheaf

open CategoryTheory Opposite TopologicalSpace
open CausalAlgebra CausalPrimality CSpecSheaf CSpecActualSheaf

universe u v

variable {k : Type u} [Field k] (C : CAlg.{u, v} k)

/-! ## The ring carried by a finite causal corner -/

@[ext]
theorem CornerElt.ext {S : Finset C.Λ} {M N : CornerElt C S}
    (h : M.mat = N.mat) : M = N := by
  cases M
  cases N
  cases h
  rfl

def cornerZero {S : Finset C.Λ} : CornerElt C S where
  mat := 0
  causal := by simp
  support := by simp

def cornerAdd {S : Finset C.Λ} (M N : CornerElt C S) : CornerElt C S where
  mat a b := M.mat a b + N.mat a b
  causal a b hab := by rw [M.causal a b hab, N.causal a b hab, add_zero]
  support a b hout := by rw [M.support a b hout, N.support a b hout, add_zero]

def cornerNeg {S : Finset C.Λ} (M : CornerElt C S) : CornerElt C S where
  mat a b := -M.mat a b
  causal a b hab := by rw [M.causal a b hab, neg_zero]
  support a b hout := by rw [M.support a b hout, neg_zero]

/-- The local identity is the diagonal idempotent supported on `S`. -/
def cornerOne {S : Finset C.Λ} : CornerElt C S where
  mat a b := if a = b ∧ a ∈ S then 1 else 0
  causal a b hab := by
    by_cases hEq : a = b
    · subst b
      exact False.elim (hab (C.le_refl a))
    · simp [hEq]
  support a b hout := by
    rcases hout with ha | hb
    · simp [ha]
    · by_cases hEq : a = b
      · subst b
        simp [hb]
      · simp [hEq]

instance {S : Finset C.Λ} : Zero (CornerElt C S) := ⟨cornerZero C⟩
instance {S : Finset C.Λ} : Add (CornerElt C S) := ⟨cornerAdd C⟩
instance {S : Finset C.Λ} : Neg (CornerElt C S) := ⟨cornerNeg C⟩
instance {S : Finset C.Λ} : Sub (CornerElt C S) := ⟨fun M N => cornerAdd C M (cornerNeg C N)⟩
instance {S : Finset C.Λ} : Mul (CornerElt C S) := ⟨cornerMul C⟩
instance {S : Finset C.Λ} : One (CornerElt C S) := ⟨cornerOne C⟩

@[simp] theorem corner_zero_mat {S : Finset C.Λ} (a b : C.Λ) :
    (0 : CornerElt C S).mat a b = 0 := rfl

@[simp] theorem corner_add_mat {S : Finset C.Λ} (M N : CornerElt C S) (a b : C.Λ) :
    (M + N).mat a b = M.mat a b + N.mat a b := rfl

@[simp] theorem corner_neg_mat {S : Finset C.Λ} (M : CornerElt C S) (a b : C.Λ) :
    (-M).mat a b = -M.mat a b := rfl

@[simp] theorem corner_sub_mat {S : Finset C.Λ} (M N : CornerElt C S) (a b : C.Λ) :
    (M - N).mat a b = M.mat a b - N.mat a b := by
  change M.mat a b + -N.mat a b = M.mat a b - N.mat a b
  rw [sub_eq_add_neg]

@[simp] theorem corner_mul_mat {S : Finset C.Λ} (M N : CornerElt C S) (a b : C.Λ) :
    (M * N).mat a b = ∑ x : C.Λ, M.mat a x * N.mat x b := rfl

@[simp] theorem corner_one_mat {S : Finset C.Λ} (a b : C.Λ) :
    (1 : CornerElt C S).mat a b = if a = b ∧ a ∈ S then 1 else 0 := rfl

/-- The additive structure is inherited pointwise from the coefficient
field. -/
instance cornerAddCommGroup {S : Finset C.Λ} : AddCommGroup (CornerElt C S) where
  add_assoc M N P := by
    apply CornerElt.ext
    funext a b
    simp [add_assoc]
  zero_add M := by
    apply CornerElt.ext
    funext a b
    simp
  add_zero M := by
    apply CornerElt.ext
    funext a b
    simp
  add_comm M N := by
    apply CornerElt.ext
    funext a b
    simp [add_comm]
  neg_add_cancel M := by
    apply CornerElt.ext
    funext a b
    simp
  sub_eq_add_neg M N := by
    apply CornerElt.ext
    funext a b
    simp
    exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Causal corners are unital rings.  Multiplication is generally
noncommutative, so `RingCat` rather than `CommRingCat` is the correct target. -/
instance cornerRing {S : Finset C.Λ} : Ring (CornerElt C S) where
  mul_assoc M N P := by
    apply CornerElt.ext
    funext a b
    simp only [corner_mul_mat]
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  one_mul M := by
    apply CornerElt.ext
    funext a b
    by_cases ha : a ∈ S
    · simp [ha]
    · rw [M.support a b (Or.inl ha)]
      simp [ha]
  mul_one M := by
    apply CornerElt.ext
    funext a b
    simp only [corner_mul_mat, corner_one_mat, mul_ite, mul_one, mul_zero]
    by_cases hb : b ∈ S
    · have hiff : ∀ x : C.Λ, (x = b ∧ x ∈ S) ↔ x = b := by
        intro x
        constructor
        · exact And.left
        · intro hxb
          exact ⟨hxb, hxb ▸ hb⟩
      simp_rw [hiff]
      simp
    · have hfalse : ∀ x : C.Λ, ¬(x = b ∧ x ∈ S) := by
        intro x hx
        exact hb (hx.1 ▸ hx.2)
      simp only [if_neg (hfalse _), Finset.sum_const_zero]
      exact (M.support a b (Or.inr hb)).symm
  left_distrib M N P := by
    apply CornerElt.ext
    funext a b
    simp only [corner_mul_mat, corner_add_mat]
    simp_rw [mul_add, Finset.sum_add_distrib]
  right_distrib M N P := by
    apply CornerElt.ext
    funext a b
    simp only [corner_mul_mat, corner_add_mat]
    simp_rw [add_mul, Finset.sum_add_distrib]
  zero_mul M := by
    apply CornerElt.ext
    funext a b
    simp
  mul_zero M := by
    apply CornerElt.ext
    funext a b
    simp

/-- Expose the ring instance through the point-fibre abbreviation used by the
sheaf construction. -/
noncomputable instance causalCornerFiberRing (P : CSpecTop C) :
    Ring (causalCornerFiber C P) := by
  unfold causalCornerFiber
  infer_instance

/-! ## The ring-valued sheaf -/

noncomputable def restrictionRingHom
    {U V : (Opens (CSpecTop C))ᵒᵖ} (i : U ⟶ V) :
    (∀ P : U.unop, causalCornerFiber C P) →+*
      (∀ P : V.unop, causalCornerFiber C P) where
  toFun s P := s (i.unop P)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Pointwise causal-corner rings on opens, with ordinary restriction. -/
noncomputable def causalCornerRingPresheaf :
    (CSpecTop C).Presheaf RingCat.{max u v} where
  obj U := RingCat.of (∀ P : U.unop, causalCornerFiber C P)
  map i := RingCat.ofHom (restrictionRingHom C i)
  map_id U := by
    ext s
    rfl
  map_comp i j := by
    ext s
    rfl

/-- Forgetting the ring operations recovers exactly the earlier sheaf-of-types
presheaf. -/
theorem causalCornerRingPresheaf_forget :
    causalCornerRingPresheaf C ⋙ CategoryTheory.forget RingCat.{max u v} =
      (causalCornerSheaf C).presheaf := by
  apply CategoryTheory.Functor.ext
  · intro U V i
    rfl
  · intro U
    rfl

/-- The genuine sheaf of noncommutative causal-corner rings on CSpec. -/
noncomputable def causalCornerRingSheaf :
    (CSpecTop C).Sheaf RingCat.{max u v} := by
  refine ⟨causalCornerRingPresheaf C, ?_⟩
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (CategoryTheory.forget RingCat.{max u v}) (causalCornerRingPresheaf C)).mpr
  rw [causalCornerRingPresheaf_forget C]
  exact causalCornerSheaf_isSheaf C

theorem causalCornerRingSheaf_isSheaf :
    (causalCornerRingSheaf C).presheaf.IsSheaf :=
  (causalCornerRingSheaf C).2

@[simp]
theorem causalCornerRingSheaf_obj (U : Opens (CSpecTop C)) :
    (causalCornerRingSheaf C).presheaf.obj (op U) =
      RingCat.of (∀ P : U, causalCornerFiber C P) :=
  rfl

end CausalAlgebraicGeometry.CSpecRingSheaf
