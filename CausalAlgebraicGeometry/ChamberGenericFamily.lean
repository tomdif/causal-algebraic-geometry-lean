/-
  ChamberGenericFamily.lean — A one-parameter chamber family.

  For a fixed combinatorial shape `d`, the recurrence coefficients make sense
  with the dimension variable replaced by a parameter `δ` in any field.  The
  rational chamber polynomial is recovered at `δ = d`; taking
  `δ = RatFunc.X` produces a genuine generic polynomial over `ℚ(δ)`.

  This module establishes the family and its degree.  Proving that its generic
  residual Galois group is symmetric is deliberately left as a named Prop.
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.PolynomialGaloisGroup
import CausalAlgebraicGeometry.ChamberGaloisBridge

namespace CausalAlgebraicGeometry.ChamberGenericFamily

open Polynomial
open CausalAlgebraicGeometry.ChamberGaloisBridge

variable {K : Type*} [Field K]

noncomputable def parameterDiag (d k : ℕ) : K :=
  if k = 0 then 1 / 3
  else if k + 1 < d - 1 then 2 / 5
  else 1 / 5

noncomputable def parameterB1Sq (δ : K) : K := 1 / (5 * (δ + 1))

noncomputable def parameterCInt (δ : K) : K := 3 / (10 * (δ - 2))

noncomputable def parameterXInt (δ : K) : K :=
  (δ - 1) / (δ + 1) - 2 / 5 - parameterCInt δ

noncomputable def parameterBIntSq (δ : K) : K :=
  parameterCInt δ * parameterXInt δ

noncomputable def parameterBLastSq (δ : K) : K :=
  ((δ - 1) / (δ + 1) - 1 / 5) * parameterXInt δ

noncomputable def parameterTopZero (δ : K) : K := (δ - 1) / (δ + 1)

/-- The fixed-shape chamber recurrence with a freely varying coefficient
parameter `δ`. -/
noncomputable def parameterChamberPolyP (d : ℕ) (δ : K) : ℕ → Polynomial K
  | 0 => 1
  | 1 => X - C (1 / 3)
  | n + 2 =>
      (X - C (parameterDiag d (n + 1))) * parameterChamberPolyP d δ (n + 1)
        - C (if n = 0 then parameterB1Sq δ
             else if n + 1 < d - 2 then parameterBIntSq δ
             else parameterBLastSq δ) * parameterChamberPolyP d δ n

noncomputable def parameterChamberPolynomial (d : ℕ) (δ : K) : Polynomial K :=
  parameterChamberPolyP d δ (d - 1)

theorem isMonicOfDegree_parameterChamberPolyP (d : ℕ) (δ : K) :
    ∀ n : ℕ, IsMonicOfDegree (parameterChamberPolyP d δ n) n := by
  suffices h : ∀ n : ℕ,
      IsMonicOfDegree (parameterChamberPolyP d δ n) n ∧
      IsMonicOfDegree (parameterChamberPolyP d δ (n + 1)) (n + 1) from
    fun n => (h n).1
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · show IsMonicOfDegree (1 : Polynomial K) 0
        rw [isMonicOfDegree_zero_iff]
      · exact isMonicOfDegree_X_sub_one (1 / 3 : K)
  | succ n ih =>
      refine ⟨ih.2, ?_⟩
      show IsMonicOfDegree
        ((X - C (parameterDiag d (n + 1))) * parameterChamberPolyP d δ (n + 1)
          - C (if n = 0 then parameterB1Sq δ
               else if n + 1 < d - 2 then parameterBIntSq δ
               else parameterBLastSq δ) * parameterChamberPolyP d δ n)
        (n + 2)
      have hmain : IsMonicOfDegree
          ((X - C (parameterDiag d (n + 1))) * parameterChamberPolyP d δ (n + 1))
          (n + 2) := by
        have hlinear : IsMonicOfDegree
            (X - C (parameterDiag d (n + 1)) : Polynomial K) 1 :=
          isMonicOfDegree_X_sub_one _
        simpa [Nat.add_comm 1 (n + 1)] using hlinear.mul ih.2
      apply hmain.sub
      calc
        (C (if n = 0 then parameterB1Sq δ
            else if n + 1 < d - 2 then parameterBIntSq δ
            else parameterBLastSq δ) * parameterChamberPolyP d δ n).natDegree
            ≤ (parameterChamberPolyP d δ n).natDegree := natDegree_C_mul_le _ _
        _ = n := ih.1.natDegree_eq
        _ < n + 2 := by omega

theorem parameterChamberPolynomial_monic (d : ℕ) (δ : K) :
    (parameterChamberPolynomial d δ).Monic :=
  (isMonicOfDegree_parameterChamberPolyP d δ (d - 1)).monic

theorem parameterChamberPolynomial_natDegree (d : ℕ) (δ : K) :
    (parameterChamberPolynomial d δ).natDegree = d - 1 :=
  (isMonicOfDegree_parameterChamberPolyP d δ (d - 1)).natDegree_eq

/-! ## Rational specialization -/

/-- At the arithmetic parameter `δ = d`, the parameterized recurrence is
definitionally the rational chamber recurrence, up to unfolding names. -/
theorem parameterChamberPolyP_specializes_to_q (d n : ℕ) :
    parameterChamberPolyP d (d : ℚ) n = qChamberPolyP d n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [parameterChamberPolyP, qChamberPolyP]
  | one => simp [parameterChamberPolyP, qChamberPolyP]
  | more n ih ih1 =>
      simp only [parameterChamberPolyP, qChamberPolyP]
      rw [ih, ih1]
      by_cases h0 : n = 0
      · simp [h0, parameterDiag, qChamberDiag, parameterB1Sq, qB1Sq]
      · by_cases h1 : n + 1 < d - 2
        · simp [h0, h1, parameterDiag, qChamberDiag, parameterBIntSq,
            qBIntSq, parameterCInt, qCInt, parameterXInt, qXInt]
        · simp [h0, h1, parameterDiag, qChamberDiag, parameterBLastSq,
            qBLastSq, parameterXInt, qXInt, parameterCInt, qCInt]

theorem parameterChamberPolynomial_specializes_to_q (d : ℕ) :
    parameterChamberPolynomial d (d : ℚ) = qChamberPolynomial d :=
  parameterChamberPolyP_specializes_to_q d (d - 1)

/-! ## The generic polynomial over ℚ(δ) -/

noncomputable def genericChamberPolynomial (d : ℕ) : Polynomial (RatFunc ℚ) :=
  parameterChamberPolynomial d RatFunc.X

noncomputable def genericResidualChamberPolynomial (d : ℕ) : Polynomial (RatFunc ℚ) :=
  genericChamberPolynomial d /ₘ (X - C (parameterTopZero RatFunc.X))

theorem genericChamberPolynomial_natDegree (d : ℕ) :
    (genericChamberPolynomial d).natDegree = d - 1 :=
  parameterChamberPolynomial_natDegree d RatFunc.X

theorem genericResidualChamberPolynomial_natDegree (d : ℕ) :
    (genericResidualChamberPolynomial d).natDegree = d - 2 := by
  rw [genericResidualChamberPolynomial,
    natDegree_divByMonic _ (monic_X_sub_C _),
    genericChamberPolynomial_natDegree, natDegree_X_sub_C]
  omega

/-- The missing generic structural-root assertion.  Once proved, the generic
residual is an actual factor rather than merely the monic quotient. -/
def GenericStructuralRootStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    (genericChamberPolynomial d).IsRoot (parameterTopZero RatFunc.X)

/-- The generic full-symmetric target over the rational-function field. -/
def GenericChamberGaloisConjecture : Prop :=
  ∀ d : ℕ, 4 ≤ d →
    let p := genericResidualChamberPolynomial d
    Function.Surjective
      (MulAction.toPermHom p.Gal (p.rootSet p.SplittingField))

end CausalAlgebraicGeometry.ChamberGenericFamily
