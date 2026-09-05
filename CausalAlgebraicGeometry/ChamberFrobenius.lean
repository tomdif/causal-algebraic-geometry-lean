/-
  ChamberFrobenius.lean — Replayable finite-field certificates for chamber
  polynomials.

  This file defines the data boundary needed to replace external Frobenius
  computations by kernel-checked objects: an integral model of a rational
  residual polynomial, its reduction modulo a certified prime, and an
  explicit irreducible factorization pattern.  The final characteristic-zero
  theorem connecting good reduction to a Galois cycle is kept as a named Prop.
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import CausalAlgebraicGeometry.ChamberGaloisBridge
import CausalAlgebraicGeometry.ChamberQ4Irreducible

namespace CausalAlgebraicGeometry.ChamberFrobenius

open Polynomial
open CausalAlgebraicGeometry.ChamberGaloisBridge

/-! ## Integral models and reduction -/

/-- An integer polynomial equal, after extension to ℚ, to a nonzero scalar
multiple of the residual chamber polynomial. -/
structure ChamberIntegralModel (d : ℕ) where
  poly : Polynomial ℤ
  scale : ℚ
  scale_ne_zero : scale ≠ 0
  map_eq : poly.map (Int.castRingHom ℚ) = C scale * qResidualChamberPolynomial d

theorem ChamberIntegralModel.natDegree {d : ℕ} (M : ChamberIntegralModel d) :
    M.poly.natDegree = d - 2 := by
  have hmap : (M.poly.map (Int.castRingHom ℚ)).natDegree = M.poly.natDegree :=
    natDegree_map_eq_of_injective Int.cast_injective M.poly
  rw [M.map_eq, natDegree_C_mul M.scale_ne_zero,
    qResidualChamberPolynomial_natDegree] at hmap
  exact hmap.symm

/-- Reduction of an integral chamber model modulo `p`. -/
noncomputable def reduceMod (p : ℕ) {d : ℕ} (M : ChamberIntegralModel d) :
    Polynomial (ZMod p) :=
  M.poly.map (Int.castRingHom (ZMod p))

/-! ## Explicit factorization certificates -/

private theorem natDegree_list_prod_of_irreducible
    {F : Type*} [Field F] (fs : List (Polynomial F))
    (hirr : ∀ f ∈ fs, Irreducible f) :
    fs.prod.natDegree = (fs.map Polynomial.natDegree).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      have hf : f ≠ 0 := (hirr f (by simp)).ne_zero
      have htail : ∀ g ∈ fs, Irreducible g := by
        intro g hg
        exact hirr g (by simp [hg])
      have hprod : fs.prod ≠ 0 := by
        apply List.prod_ne_zero
        intro hzero
        exact (htail 0 hzero).ne_zero rfl
      rw [List.prod_cons, natDegree_mul' (by simp [hf, hprod]), List.map_cons,
        List.sum_cons, ih htail]

/-- A factorization pattern certified entirely by explicit polynomial data.

`unit * factors.prod = reduceMod p model` permits non-monic integral models;
the list of degrees is the Frobenius cycle-pattern input used downstream. -/
structure FrobeniusFactorCertificate (d p : ℕ) (pattern : List ℕ) where
  prime : p.Prime
  model : ChamberIntegralModel d
  unit : ZMod p
  unit_ne_zero : unit ≠ 0
  factors : List (Polynomial (ZMod p))
  factorization : C unit * factors.prod = reduceMod p model
  irreducible : ∀ f ∈ factors, Irreducible f
  /-- Distinct listed factors are coprime, excluding repeated factors and
  therefore ramified reduction. -/
  pairwise_coprime : factors.Pairwise IsCoprime
  good_degree : (reduceMod p model).natDegree = d - 2
  degree_pattern : factors.map Polynomial.natDegree = pattern

/-- A valid factorization certificate has total cycle length `d - 2`. -/
theorem FrobeniusFactorCertificate.pattern_sum
    {d p : ℕ} {pattern : List ℕ}
    (cert : FrobeniusFactorCertificate d p pattern) :
    pattern.sum = d - 2 := by
  letI : Fact p.Prime := ⟨cert.prime⟩
  have hprod := natDegree_list_prod_of_irreducible cert.factors cert.irreducible
  have hscale : (C cert.unit * cert.factors.prod).natDegree =
      cert.factors.prod.natDegree := natDegree_C_mul cert.unit_ne_zero
  calc
    pattern.sum = (cert.factors.map Polynomial.natDegree).sum := by
      rw [cert.degree_pattern]
    _ = cert.factors.prod.natDegree := hprod.symm
    _ = (C cert.unit * cert.factors.prod).natDegree := hscale.symm
    _ = (reduceMod p cert.model).natDegree := congrArg Polynomial.natDegree cert.factorization
    _ = d - 2 := cert.good_degree

/-- A certified prime-cycle length occurs as one entry in the finite-field
factor-degree pattern. -/
def HasCertifiedCycleLength {d p : ℕ} {pattern : List ℕ}
    (_cert : FrobeniusFactorCertificate d p pattern) (q : ℕ) : Prop :=
  q ∈ pattern

/-! ## A concrete seed computation -/

private instance prime11Fact : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The integral form of the already formalized rational quadratic `Q4`. -/
noncomputable def q4Integral : Polynomial ℤ := 150 * X ^ 2 - 50 * X + 3

theorem q4Integral_map_rat :
    q4Integral.map (Int.castRingHom ℚ) = ChamberQ4.Q4 := by
  simp [q4Integral, ChamberQ4.Q4]

/-- In dimension four, the rational residual chamber polynomial is exactly
the monic normalization of `Q4`. -/
theorem qResidualChamberPolynomial_four :
    C (150 : ℚ) * qResidualChamberPolynomial 4 = ChamberQ4.Q4 := by
  have hchamber : qChamberPolynomial 4 =
      (X - C (qTopZero 4)) * (C (1 / 150 : ℚ) * ChamberQ4.Q4) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have heval : ∀ x : ℚ,
        eval x (qChamberPolynomial 4) =
          eval x ((X - C (qTopZero 4)) *
            (C (1 / 150 : ℚ) * ChamberQ4.Q4)) := by
      intro x
      norm_num [qChamberPolynomial, qChamberPolyP, qChamberDiag, qB1Sq,
        qBLastSq, qXInt, qCInt, qTopZero, ChamberQ4.Q4]
      ring
    simpa [heval] using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℚ))
  have hresidual : qResidualChamberPolynomial 4 =
      C (1 / 150 : ℚ) * ChamberQ4.Q4 := by
    rw [qResidualChamberPolynomial, hchamber,
      mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
  rw [hresidual]
  rw [← mul_assoc, ← C_mul]
  norm_num

/-- The integral `Q4` is therefore a genuine model of the `d = 4` residual
chamber polynomial. -/
noncomputable def q4IntegralModel : ChamberIntegralModel 4 where
  poly := q4Integral
  scale := 150
  scale_ne_zero := by norm_num
  map_eq := by
    rw [q4Integral_map_rat, qResidualChamberPolynomial_four]

/-- Reduction of `Q4` at the good prime 11. -/
noncomputable def q4Mod11 : Polynomial (ZMod 11) :=
  C 7 * X ^ 2 + C 5 * X + C 3

theorem q4Mod11_natDegree : q4Mod11.natDegree = 2 := by
  unfold q4Mod11
  compute_degree!

theorem q4Mod11_no_root : ∀ x : ZMod 11, ¬q4Mod11.IsRoot x := by
  intro x
  fin_cases x <;> norm_num [Polynomial.IsRoot.def, q4Mod11] <;> native_decide

/-- The mod-11 polynomial is irreducible, giving the degree pattern `[2]`. -/
theorem q4Mod11_irreducible : Irreducible q4Mod11 := by
  have hdegree : q4Mod11.natDegree ∈ Finset.Icc 1 3 := by
    rw [Finset.mem_Icc, q4Mod11_natDegree]
    omega
  exact @Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (ZMod 11) inferInstance q4Mod11 hdegree q4Mod11_no_root

theorem q4Mod11_eq_reduceMod :
    q4Mod11 = reduceMod 11 q4IntegralModel := by
  simp [reduceMod, q4IntegralModel, q4Integral]
  change q4Mod11 =
    C (150 : ZMod 11) * X ^ 2 - C (50 : ZMod 11) * X + C (3 : ZMod 11)
  have h150 : (150 : ZMod 11) = 7 := by native_decide
  have h50 : (50 : ZMod 11) = -5 := by native_decide
  rw [h150, h50]
  simp [q4Mod11]

/-- A complete replayable factorization certificate for the first residual
chamber case. -/
noncomputable def q4Mod11Certificate :
    FrobeniusFactorCertificate 4 11 [2] where
  prime := by norm_num
  model := q4IntegralModel
  unit := 1
  unit_ne_zero := one_ne_zero
  factors := [q4Mod11]
  factorization := by simp [q4Mod11_eq_reduceMod]
  irreducible := by
    intro f hf
    simp only [List.mem_singleton] at hf
    simpa [hf] using q4Mod11_irreducible
  pairwise_coprime := by simp
  good_degree := by
    rw [← q4Mod11_eq_reduceMod]
    exact q4Mod11_natDegree
  degree_pattern := by simp [q4Mod11_natDegree]

/-- The exact missing theorem needed to turn a squarefree factor pattern into
the corresponding element of the characteristic-zero chamber Galois group.

Mathlib's `cycleType` omits fixed points, so degree-one factors are filtered
from the pattern.  `pairwise_coprime` is essential: without it a repeated
factor would represent ramified reduction and no Frobenius cycle type.  This
is intentionally a target, not an axiom. -/
def FrobeniusCycleBridgeStatement : Prop := by
  classical
  exact
    ∀ {d p : ℕ} {pattern : List ℕ},
      (cert : FrobeniusFactorCertificate d p pattern) →
      ∃ σ : (qResidualChamberPolynomial d).Gal,
        (chamberGaloisActionHom d σ).cycleType =
          (pattern.filter fun degree => degree ≠ 1)

end CausalAlgebraicGeometry.ChamberFrobenius
