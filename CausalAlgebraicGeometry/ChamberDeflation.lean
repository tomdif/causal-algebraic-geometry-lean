/-
  ChamberDeflation.lean — Deflation of the chamber characteristic polynomial.

  Provides:
    - chamberPolynomial d : Polynomial ℝ (formal polynomial mirroring chamberPoly)
    - eval_chamberPolynomial: agreement with the recurrence definition
    - monic_chamberPolynomial, natDegree_chamberPolynomial
    - chamber_deflation_of_root: char(J_d) = (X - C λ) · Q with deg Q = d - 2
      whenever λ is a root
    - chamber_deflation_d3: unconditional d=3 instance using topZero_is_zero_d3
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import CausalAlgebraicGeometry.ChamberPolynomials

namespace CausalAlgebraicGeometry.ChamberPolynomials

open Polynomial

noncomputable def chamberPolyP (d : ℕ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C (1 / 3)
  | (n + 2) =>
      (Polynomial.X - Polynomial.C (chamberDiag d (n + 1))) * chamberPolyP d (n + 1)
        - Polynomial.C
            (if n = 0 then b1sq d
             else if n + 1 < d - 2 then bint_sq d
             else blast_sq d) * chamberPolyP d n

noncomputable def chamberPolynomial (d : ℕ) : Polynomial ℝ :=
  chamberPolyP d (d - 1)

theorem eval_chamberPolyP (d : ℕ) (x : ℝ) :
    ∀ n : ℕ, (chamberPolyP d n).eval x = chamberPoly d x n := by
  suffices h : ∀ n : ℕ,
      (chamberPolyP d n).eval x = chamberPoly d x n ∧
      (chamberPolyP d (n + 1)).eval x = chamberPoly d x (n + 1) from
    fun n => (h n).1
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · simp [chamberPolyP, chamberPoly]
      · simp [chamberPolyP, chamberPoly]
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      simp only [chamberPolyP, chamberPoly, eval_sub, eval_mul, eval_X, eval_C]
      rw [ih.1, ih.2]

theorem isMonicOfDegree_chamberPolyP (d : ℕ) :
    ∀ n : ℕ, IsMonicOfDegree (chamberPolyP d n) n := by
  suffices h : ∀ n : ℕ,
      IsMonicOfDegree (chamberPolyP d n) n ∧
      IsMonicOfDegree (chamberPolyP d (n + 1)) (n + 1) from
    fun n => (h n).1
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · show IsMonicOfDegree (1 : Polynomial ℝ) 0
        rw [isMonicOfDegree_zero_iff]
      · show IsMonicOfDegree (Polynomial.X - Polynomial.C (1 / 3 : ℝ)) 1
        exact isMonicOfDegree_X_sub_one (1 / 3 : ℝ)
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show IsMonicOfDegree
        ((Polynomial.X - Polynomial.C (chamberDiag d (k + 1))) * chamberPolyP d (k + 1)
          - Polynomial.C
              (if k = 0 then b1sq d
               else if k + 1 < d - 2 then bint_sq d
               else blast_sq d) * chamberPolyP d k)
        (k + 2)
      have hmul : IsMonicOfDegree
          ((Polynomial.X - Polynomial.C (chamberDiag d (k + 1))) * chamberPolyP d (k + 1))
          (k + 2) := by
        have h1 : IsMonicOfDegree
            (Polynomial.X - Polynomial.C (chamberDiag d (k + 1))) 1 :=
          isMonicOfDegree_X_sub_one _
        have h2 := ih.2
        have hprod := h1.mul h2
        simpa [Nat.add_comm 1 (k + 1)] using hprod
      have hsub_lt : (Polynomial.C
          (if k = 0 then b1sq d
           else if k + 1 < d - 2 then bint_sq d
           else blast_sq d) * chamberPolyP d k).natDegree < k + 2 := by
        have hPk_deg : (chamberPolyP d k).natDegree = k := ih.1.natDegree_eq
        calc (Polynomial.C _ * chamberPolyP d k).natDegree
            ≤ (chamberPolyP d k).natDegree := natDegree_C_mul_le _ _
          _ = k := hPk_deg
          _ < k + 2 := by omega
      exact hmul.sub hsub_lt

theorem natDegree_chamberPolyP (d n : ℕ) : (chamberPolyP d n).natDegree = n :=
  (isMonicOfDegree_chamberPolyP d n).natDegree_eq

theorem monic_chamberPolyP (d n : ℕ) : (chamberPolyP d n).Monic :=
  (isMonicOfDegree_chamberPolyP d n).monic

theorem natDegree_chamberPolynomial (d : ℕ) :
    (chamberPolynomial d).natDegree = d - 1 :=
  natDegree_chamberPolyP d (d - 1)

theorem monic_chamberPolynomial (d : ℕ) : (chamberPolynomial d).Monic :=
  monic_chamberPolyP d (d - 1)

theorem eval_chamberPolynomial (d : ℕ) (x : ℝ) :
    (chamberPolynomial d).eval x = chamberPoly d x (d - 1) :=
  eval_chamberPolyP d x (d - 1)

theorem chamber_deflation_of_root (d : ℕ) (hd : 1 ≤ d) (lam : ℝ)
    (hroot : (chamberPolynomial d).IsRoot lam) :
    ∃ Q : Polynomial ℝ,
      chamberPolynomial d = (Polynomial.X - Polynomial.C lam) * Q ∧
      Q.natDegree = d - 2 := by
  obtain ⟨Q, hQ⟩ :=
    (Polynomial.dvd_iff_isRoot (a := lam) (p := chamberPolynomial d)).mpr hroot
  refine ⟨Q, hQ, ?_⟩
  have hX : (Polynomial.X - Polynomial.C lam : Polynomial ℝ).natDegree = 1 :=
    natDegree_X_sub_C lam
  have hMonicX : (Polynomial.X - Polynomial.C lam : Polynomial ℝ).Monic :=
    monic_X_sub_C lam
  have hMonicChamber : (chamberPolynomial d).Monic := monic_chamberPolynomial d
  have hChamber_ne : chamberPolynomial d ≠ 0 := hMonicChamber.ne_zero
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    apply hChamber_ne
    rw [hQ, hQ0, mul_zero]
  have hND_prod :
      ((Polynomial.X - Polynomial.C lam) * Q).natDegree = 1 + Q.natDegree := by
    rw [hMonicX.natDegree_mul' hQ_ne, hX]
  have hND_chamber : (chamberPolynomial d).natDegree = d - 1 :=
    natDegree_chamberPolynomial d
  have heq : 1 + Q.natDegree = d - 1 := by
    rw [← hND_prod, ← hQ]; exact hND_chamber
  omega

theorem chamber_deflation_d3 :
    ∃ Q : Polynomial ℝ,
      chamberPolynomial 3 =
        (Polynomial.X - Polynomial.C ((3 - 1 : ℝ) / (3 + 1))) * Q ∧
      Q.natDegree = 3 - 2 := by
  have hroot_fun : chamberPoly 3 (topZero 3) 2 = 0 := topZero_is_zero_d3
  have hroot : (chamberPolynomial 3).IsRoot (topZero 3) := by
    show (chamberPolynomial 3).eval (topZero 3) = 0
    have h := eval_chamberPolynomial 3 (topZero 3)
    rw [h]; simpa using hroot_fun
  have htop : topZero 3 = ((3 - 1 : ℝ) / (3 + 1)) := by
    unfold topZero; norm_num
  rw [← htop]
  exact chamber_deflation_of_root 3 (by norm_num) (topZero 3) hroot

end CausalAlgebraicGeometry.ChamberPolynomials
