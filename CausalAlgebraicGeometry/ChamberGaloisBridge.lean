/-
  ChamberGaloisBridge.lean — Rational chamber polynomials and their genuine
  splitting-field Galois actions.

  The analytic chamber development uses real coefficients.  Galois theory,
  however, needs a polynomial over a field such as ℚ.  This file defines the
  same recurrence over ℚ, proves that coefficient extension to ℝ recovers the
  existing polynomial, deflates its structural rational root, and states the
  full-symmetric-group target using Mathlib's `Polynomial.Gal` API.
-/
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.AlgebraMap
import CausalAlgebraicGeometry.ChamberStructuralRoot

namespace CausalAlgebraicGeometry.ChamberGaloisBridge

open Polynomial
open CausalAlgebraicGeometry.ChamberPolynomials

/-! ## The chamber recurrence over ℚ -/

noncomputable def qChamberDiag (d k : ℕ) : ℚ :=
  if k = 0 then 1 / 3
  else if k + 1 < d - 1 then 2 / 5
  else 1 / 5

noncomputable def qB1Sq (d : ℕ) : ℚ := 1 / (5 * ((d : ℚ) + 1))

noncomputable def qCInt (d : ℕ) : ℚ := 3 / (10 * ((d : ℚ) - 2))

noncomputable def qXInt (d : ℕ) : ℚ :=
  ((d : ℚ) - 1) / ((d : ℚ) + 1) - 2 / 5 - qCInt d

noncomputable def qBIntSq (d : ℕ) : ℚ := qCInt d * qXInt d

noncomputable def qBLastSq (d : ℕ) : ℚ :=
  (((d : ℚ) - 1) / ((d : ℚ) + 1) - 1 / 5) * qXInt d

/-- The distinguished structural root, before embedding into ℝ. -/
noncomputable def qTopZero (d : ℕ) : ℚ := ((d : ℚ) - 1) / ((d : ℚ) + 1)

/-- The chamber polynomial recurrence over ℚ. -/
noncomputable def qChamberPolyP (d : ℕ) : ℕ → Polynomial ℚ
  | 0 => 1
  | 1 => X - C (1 / 3)
  | n + 2 =>
      (X - C (qChamberDiag d (n + 1))) * qChamberPolyP d (n + 1)
        - C (if n = 0 then qB1Sq d
             else if n + 1 < d - 2 then qBIntSq d
             else qBLastSq d) * qChamberPolyP d n

/-- The degree-`d - 1` chamber polynomial over ℚ. -/
noncomputable def qChamberPolynomial (d : ℕ) : Polynomial ℚ :=
  qChamberPolyP d (d - 1)

/-! ## Compatibility with the existing real development -/

@[simp] theorem qChamberDiag_cast (d k : ℕ) :
    ((qChamberDiag d k : ℚ) : ℝ) = chamberDiag d k := by
  by_cases h0 : k = 0
  · simp [qChamberDiag, chamberDiag, h0]
  · by_cases h1 : k + 1 < d - 1
    · simp [qChamberDiag, chamberDiag, h0, h1]
    · simp [qChamberDiag, chamberDiag, h0, h1]

@[simp] theorem qB1Sq_cast (d : ℕ) : ((qB1Sq d : ℚ) : ℝ) = b1sq d := by
  simp [qB1Sq, b1sq]

@[simp] theorem qCInt_cast (d : ℕ) : ((qCInt d : ℚ) : ℝ) = Cint d := by
  simp [qCInt, Cint]

@[simp] theorem qXInt_cast (d : ℕ) : ((qXInt d : ℚ) : ℝ) = xint d := by
  simp [qXInt, xint]

@[simp] theorem qBIntSq_cast (d : ℕ) : ((qBIntSq d : ℚ) : ℝ) = bint_sq d := by
  simp [qBIntSq, bint_sq]

@[simp] theorem qBLastSq_cast (d : ℕ) : ((qBLastSq d : ℚ) : ℝ) = blast_sq d := by
  simp [qBLastSq, blast_sq]

@[simp] theorem qTopZero_cast (d : ℕ) : ((qTopZero d : ℚ) : ℝ) = topZero d := by
  simp [qTopZero, topZero]

/-- Extending coefficients from ℚ to ℝ gives the original recurrence exactly. -/
theorem map_qChamberPolyP (d n : ℕ) :
    (qChamberPolyP d n).map (algebraMap ℚ ℝ) = chamberPolyP d n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [qChamberPolyP, chamberPolyP]
  | one => simp [qChamberPolyP, chamberPolyP]
  | more n ih ih1 =>
      simp only [qChamberPolyP, chamberPolyP, Polynomial.map_sub,
        Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
      rw [ih, ih1]
      by_cases h0 : n = 0
      · simp [h0]
      · by_cases h1 : n + 1 < d - 2
        · simp [h0, h1]
        · simp [h0, h1]

/-- The rational and real chamber polynomials are the same after base change. -/
theorem map_qChamberPolynomial (d : ℕ) :
    (qChamberPolynomial d).map (algebraMap ℚ ℝ) = chamberPolynomial d := by
  exact map_qChamberPolyP d (d - 1)

/-! ## Degree and structural deflation over ℚ -/

theorem isMonicOfDegree_qChamberPolyP (d : ℕ) :
    ∀ n : ℕ, IsMonicOfDegree (qChamberPolyP d n) n := by
  suffices h : ∀ n : ℕ,
      IsMonicOfDegree (qChamberPolyP d n) n ∧
      IsMonicOfDegree (qChamberPolyP d (n + 1)) (n + 1) from
    fun n => (h n).1
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · show IsMonicOfDegree (1 : Polynomial ℚ) 0
        rw [isMonicOfDegree_zero_iff]
      · show IsMonicOfDegree (X - C (1 / 3 : ℚ)) 1
        exact isMonicOfDegree_X_sub_one (1 / 3 : ℚ)
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show IsMonicOfDegree
        ((X - C (qChamberDiag d (k + 1))) * qChamberPolyP d (k + 1)
          - C (if k = 0 then qB1Sq d
               else if k + 1 < d - 2 then qBIntSq d
               else qBLastSq d) * qChamberPolyP d k)
        (k + 2)
      have hmul : IsMonicOfDegree
          ((X - C (qChamberDiag d (k + 1))) * qChamberPolyP d (k + 1))
          (k + 2) := by
        have h1 : IsMonicOfDegree (X - C (qChamberDiag d (k + 1))) 1 :=
          isMonicOfDegree_X_sub_one _
        have hprod := h1.mul ih.2
        simpa [Nat.add_comm 1 (k + 1)] using hprod
      have hsub_lt : (C
          (if k = 0 then qB1Sq d
           else if k + 1 < d - 2 then qBIntSq d
           else qBLastSq d) * qChamberPolyP d k).natDegree < k + 2 := by
        calc
          (C _ * qChamberPolyP d k).natDegree
              ≤ (qChamberPolyP d k).natDegree := natDegree_C_mul_le _ _
          _ = k := ih.1.natDegree_eq
          _ < k + 2 := by omega
      exact hmul.sub hsub_lt

theorem qChamberPolynomial_monic (d : ℕ) : (qChamberPolynomial d).Monic :=
  (isMonicOfDegree_qChamberPolyP d (d - 1)).monic

theorem qChamberPolynomial_natDegree (d : ℕ) :
    (qChamberPolynomial d).natDegree = d - 1 :=
  (isMonicOfDegree_qChamberPolyP d (d - 1)).natDegree_eq

/-- The structural root is rational; this is transported back from the already
proved real structural-root theorem through the injective map `ℚ → ℝ`. -/
theorem qChamberPolynomial_topZero_isRoot (d : ℕ) (hd : 3 ≤ d) :
    (qChamberPolynomial d).IsRoot (qTopZero d) := by
  apply Polynomial.isRoot_of_aeval_algebraMap_eq_zero (S := ℝ)
  rw [← Polynomial.eval_map_algebraMap]
  rw [map_qChamberPolynomial]
  have hz : algebraMap ℚ ℝ (qTopZero d) = topZero d := qTopZero_cast d
  rw [hz]
  exact chamberPolynomial_topZero_isRoot d hd

/-- The residual chamber polynomial after removing the structural root. -/
noncomputable def qResidualChamberPolynomial (d : ℕ) : Polynomial ℚ :=
  qChamberPolynomial d /ₘ (X - C (qTopZero d))

theorem qChamber_factorization (d : ℕ) (hd : 3 ≤ d) :
    (X - C (qTopZero d)) * qResidualChamberPolynomial d = qChamberPolynomial d := by
  exact mul_divByMonic_eq_iff_isRoot.mpr (qChamberPolynomial_topZero_isRoot d hd)

theorem qResidualChamberPolynomial_natDegree (d : ℕ) :
    (qResidualChamberPolynomial d).natDegree = d - 2 := by
  rw [qResidualChamberPolynomial, natDegree_divByMonic _ (monic_X_sub_C _),
    qChamberPolynomial_natDegree, natDegree_X_sub_C]
  omega

/-! ## The actual Galois target -/

/-- The roots in the canonical splitting field of the residual polynomial. -/
abbrev ChamberRoot (d : ℕ) :=
  (qResidualChamberPolynomial d).rootSet
    (qResidualChamberPolynomial d).SplittingField

/-- The canonical action of the splitting-field automorphism group on its
roots.  At the splitting field itself, Mathlib supplies this action directly. -/
noncomputable def chamberGaloisActionHom (d : ℕ) :
    (qResidualChamberPolynomial d).Gal →*
      Equiv.Perm (ChamberRoot d) :=
  MulAction.toPermHom _ _

/-- The chamber Galois group realizes every permutation of the residual roots.

Unlike the former abstract placeholder, both the group and its action are the
canonical objects constructed from the concrete polynomial by Mathlib. -/
def HasFullChamberGaloisGroup (d : ℕ) : Prop :=
  Function.Surjective (chamberGaloisActionHom d)

/-- The canonical action is faithful, independently of the conjectural
surjectivity assertion. -/
theorem chamberGaloisAction_faithful (d : ℕ) :
    Function.Injective (chamberGaloisActionHom d) := by
  intro σ τ hστ
  apply Polynomial.Gal.ext
  intro x hx
  have hroot := DFunLike.congr_fun hστ
    (⟨x, hx⟩ : ChamberRoot d)
  exact Subtype.ext_iff.mp hroot

/-- Irreducibility supplies the transitivity step in the usual Galois-group
argument. -/
theorem chamberGaloisAction_pretransitive (d : ℕ)
    (hirr : Irreducible (qResidualChamberPolynomial d)) :
    ∀ x y : ChamberRoot d,
      ∃ σ : (qResidualChamberPolynomial d).Gal,
        chamberGaloisActionHom d σ x = y := by
  intro x y
  have hx := minpoly.eq_of_irreducible hirr (mem_rootSet.mp x.2).2
  have hy := minpoly.eq_of_irreducible hirr (mem_rootSet.mp y.2).2
  obtain ⟨σ, hσ⟩ :=
    (Normal.minpoly_eq_iff_mem_orbit
      (qResidualChamberPolynomial d).SplittingField).mp (hy.symm.trans hx)
  exact ⟨σ, Subtype.ext hσ⟩

/-- If the residual polynomial is separable, its root set has the expected
cardinality `d - 2`.  Separability remains an explicit mathematical premise. -/
theorem chamberRoot_card (d : ℕ)
    (hsep : (qResidualChamberPolynomial d).Separable) :
    Fintype.card (ChamberRoot d) = d - 2 := by
  rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits _),
    qResidualChamberPolynomial_natDegree]

end CausalAlgebraicGeometry.ChamberGaloisBridge
