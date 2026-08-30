/-
  CodimOneInterlacing.lean — Subspace dimension intersection bound and
  codim-one Cauchy interlacing for the top eigenvalue of a Hermitian matrix.
-/
import CausalAlgebraicGeometry.CauchyInterlacing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.CodimOneInterlacing

open scoped InnerProductSpace
open Matrix Module Submodule
open CausalAlgebraicGeometry.CauchyInterlacing

variable {n : ℕ}

/-! ## Milestone 1 — subspace intersection dimension bound -/

/-- For two finite-dimensional subspaces `V W` of a finite-dimensional
ambient space of dimension `n`, the intersection has dimension at least
`dim V + dim W − n`.  Stated additively in `ℕ`, free of subtraction:

    `dim V + dim W ≤ n + dim (V ⊓ W)`.

This is a thin wrapper around `Submodule.finrank_sup_add_finrank_inf_eq`
and the bound `finrank (V ⊔ W) ≤ n`. -/
theorem add_finrank_le_finrank_inter_add
    (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Module.finrank ℝ V + Module.finrank ℝ W
      ≤ n + Module.finrank ℝ ↥(V ⊓ W) := by
  classical
  have hsum : Module.finrank ℝ ↥(V ⊔ W) + Module.finrank ℝ ↥(V ⊓ W)
      = Module.finrank ℝ V + Module.finrank ℝ W :=
    Submodule.finrank_sup_add_finrank_inf_eq V W
  have hsupLe : Module.finrank ℝ ↥(V ⊔ W) ≤ n := by
    have h := (V ⊔ W).finrank_le (R := ℝ) (M := EuclideanSpace ℝ (Fin n))
    simpa [finrank_euclideanSpace_fin] using h
  -- combine: (finrank V⊔W) + (finrank V⊓W) ≤ n + (finrank V⊓W) and rewrite LHS via hsum.
  have h := add_le_add_right hsupLe (Module.finrank ℝ ↥(V ⊓ W))
  linarith

/-! ## Milestone 2 — codim-one Cauchy interlacing for the top eigenvalue

CONVENTION NOTE.  Mathlib's `Matrix.IsHermitian.eigenvalues` (the version
indexed by the matrix's index type `n`) is, in current Mathlib, defined
via a *noncomputable* `Fintype.equivOfCardEq`, so it is **not** ordered
in any canonical way when `n = Fin k`.  The truly antitone family is
`Matrix.IsHermitian.eigenvalues₀ : Fin (Fintype.card n) → ℝ`, with
`Matrix.IsHermitian.eigenvalues₀_antitone` recorded in Mathlib.  We
therefore state the codim-one interlacing in terms of `eigenvalues₀`,
indexed by `Fin (Fintype.card (Fin n)) = Fin n`. -/

/-- Action of a Hermitian matrix on an eigenvector basis vector,
in the `EuclideanSpace`/`toEuclideanLin` form (as opposed to the
`mulVec` form recorded in Mathlib).  This mirrors the proof recipe used
in `CauchyInterlacing.rayleigh_eigenvectorBasis`. -/
lemma toEuclideanLin_eigenvectorBasis
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i : Fin n) :
    (toEuclideanLin A) (hA.eigenvectorBasis i)
      = (hA.eigenvalues i) • (hA.eigenvectorBasis i :
          EuclideanSpace ℝ (Fin n)) := by
  have hmul := hA.mulVec_eigenvectorBasis i
  apply (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective
  simp [Matrix.toEuclideanLin, WithLp.linearEquiv, hmul,
        Matrix.toLin'_apply]

/-- Quadratic form expansion of a real Hermitian matrix in an eigenbasis:
for any `v : EuclideanSpace ℝ (Fin n)` and a Hermitian `A`,

    `⟨v, A v⟩ = Σ_i (⟨e_i, v⟩)² · λ_i`,

where `e_i = hA.eigenvectorBasis i` and `λ_i = hA.eigenvalues i`. -/
lemma inner_self_apply_eq_sum_sq_eigenvalues
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, (toEuclideanLin A) v⟫_ℝ
      = ∑ i : Fin n,
          (⟪(hA.eigenvectorBasis i : EuclideanSpace ℝ (Fin n)), v⟫_ℝ) ^ 2
            * hA.eigenvalues i := by
  classical
  set b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    hA.eigenvectorBasis with hb
  -- Expand v in the eigenbasis on the *right* slot only (linearity will
  -- take care of the left slot via inner_sum).
  have hAv : (toEuclideanLin A) v
      = ∑ i, (⟪b i, v⟫_ℝ * hA.eigenvalues i) • (b i :
          EuclideanSpace ℝ (Fin n)) := by
    have hv : v = ∑ i, ⟪b i, v⟫_ℝ • b i := (b.sum_repr' v).symm
    have key : ∀ i, (toEuclideanLin A) (b i)
        = (hA.eigenvalues i) • (b i : EuclideanSpace ℝ (Fin n)) :=
      fun i => toEuclideanLin_eigenvectorBasis A hA i
    calc (toEuclideanLin A) v
        = (toEuclideanLin A) (∑ i, ⟪b i, v⟫_ℝ • b i) := by rw [← hv]
      _ = ∑ i, ⟪b i, v⟫_ℝ • (toEuclideanLin A) (b i) := by
          rw [map_sum]; simp_rw [map_smul]
      _ = ∑ i, ⟪b i, v⟫_ℝ • ((hA.eigenvalues i) • (b i :
              EuclideanSpace ℝ (Fin n))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [key i]
      _ = ∑ i, (⟪b i, v⟫_ℝ * hA.eigenvalues i) • (b i :
              EuclideanSpace ℝ (Fin n)) := by
          simp_rw [smul_smul]
  rw [hAv, inner_sum]
  -- The remaining inner product `⟪v, c · b i⟫` = `c * ⟪v, b i⟫`.
  -- Express ⟪v, b i⟫ via the OB representation again to relate it to ⟪b i, v⟫.
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right, real_inner_comm v (b i)]
  ring

/-- Pointwise upper bound: the Rayleigh quotient at any nonzero vector
is bounded above by the top eigenvalue `eigenvalues₀ 0`. -/
lemma rayleigh_le_eigenvalues_zero
    (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    rayleigh A v
      ≤ hA.eigenvalues₀ ⟨0, by simpa [Fintype.card_fin] using hn⟩ := by
  classical
  set lamMax : ℝ :=
    hA.eigenvalues₀ ⟨0, by simpa [Fintype.card_fin] using hn⟩ with hlamMax
  have h_le_max : ∀ i : Fin n, hA.eigenvalues i ≤ lamMax := by
    intro i
    show hA.eigenvalues₀ _ ≤ _
    refine hA.eigenvalues₀_antitone ?_
    show (⟨0, _⟩ : Fin (Fintype.card (Fin n))).val
        ≤ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val
    exact Nat.zero_le _
  set b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    hA.eigenvectorBasis with hb
  have hvnorm : 0 < ‖v‖ ^ 2 := by
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    positivity
  have hexp := inner_self_apply_eq_sum_sq_eigenvalues A hA v
  have hbound : ⟪v, (toEuclideanLin A) v⟫_ℝ ≤ ‖v‖ ^ 2 * lamMax := by
    rw [hexp]
    have hsum_eq : ∑ i : Fin n, (⟪b i, v⟫_ℝ) ^ 2 = ‖v‖ ^ 2 := by
      have := b.sum_sq_norm_inner_right v
      simpa [Real.norm_eq_abs, sq_abs] using this
    have hineq : ∑ i : Fin n, (⟪b i, v⟫_ℝ) ^ 2 * hA.eigenvalues i
        ≤ ∑ i : Fin n, (⟪b i, v⟫_ℝ) ^ 2 * lamMax := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (h_le_max i) (sq_nonneg _)
    refine hineq.trans ?_
    rw [← Finset.sum_mul, hsum_eq]
  rw [rayleigh, div_le_iff₀ hvnorm, mul_comm]
  exact hbound

/-- Upper bound: the maximum Rayleigh quotient over a *nontrivial*
subspace `W` is bounded above by `eigenvalues₀ 0`, the largest
eigenvalue.  The hypothesis `hW : W ≠ ⊥` is needed because
`maxRayleigh A ⊥ = 0` by convention. -/
lemma maxRayleigh_le_eigenvalues_zero
    (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hW : W ≠ ⊥) :
    maxRayleigh A W
      ≤ hA.eigenvalues₀ ⟨0, by simpa [Fintype.card_fin] using hn⟩ := by
  classical
  -- Existence of a nonzero vector in `W`.
  obtain ⟨v0, hv0W, hv0ne⟩ := (Submodule.ne_bot_iff W).1 hW
  have : Nonempty { v : W // (v : EuclideanSpace ℝ (Fin n)) ≠ 0 } :=
    ⟨⟨⟨v0, hv0W⟩, hv0ne⟩⟩
  unfold maxRayleigh
  apply ciSup_le
  rintro ⟨⟨v, _⟩, hv0⟩
  dsimp only
  exact rayleigh_le_eigenvalues_zero hn A hA v hv0

/-! ### Lower bound: pick a Rayleigh witness from `W ∩ span(top 2 eigenvectors)` -/

/-- Auxiliary computation: for orthonormal `e0, e1` in
`EuclideanSpace ℝ (Fin n)` and a `v` of the form `a • e0 + b • e1`,
the squared norm is `a² + b²`. -/
lemma sq_norm_pair_combination
    {e0 e1 : EuclideanSpace ℝ (Fin n)} (h0 : ‖e0‖ = 1) (h1 : ‖e1‖ = 1)
    (horth : ⟪e0, e1⟫_ℝ = 0) (a b : ℝ) :
    ‖a • e0 + b • e1‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have h10 : ⟪e1, e0⟫_ℝ = 0 := by rw [real_inner_comm]; exact horth
  have hself0 : ⟪e0, e0⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, h0]; ring
  have hself1 : ⟪e1, e1⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, h1]; ring
  have key : ⟪a • e0 + b • e1, a • e0 + b • e1⟫_ℝ = a ^ 2 + b ^ 2 := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
               real_inner_smul_right, hself0, hself1, horth, h10]
    ring
  have hself : ⟪a • e0 + b • e1, a • e0 + b • e1⟫_ℝ
      = ‖a • e0 + b • e1‖ ^ 2 := real_inner_self_eq_norm_sq _
  linarith

/-- Auxiliary computation: for `e0, e1` eigenvectors of `A` (Hermitian)
with eigenvalues `lam0, lam1`, the inner product `⟪v, A v⟫` for `v = a•e0 + b•e1`
is `a² lam0 + b² lam1`. -/
lemma inner_self_apply_pair_combination
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    {e0 e1 : EuclideanSpace ℝ (Fin n)} {lam0 lam1 : ℝ}
    (he0 : (toEuclideanLin A) e0 = lam0 • e0)
    (he1 : (toEuclideanLin A) e1 = lam1 • e1)
    (h0 : ‖e0‖ = 1) (h1 : ‖e1‖ = 1)
    (horth : ⟪e0, e1⟫_ℝ = 0) (a b : ℝ) :
    ⟪a • e0 + b • e1, (toEuclideanLin A) (a • e0 + b • e1)⟫_ℝ
      = a ^ 2 * lam0 + b ^ 2 * lam1 := by
  have h10 : ⟪e1, e0⟫_ℝ = 0 := by rw [real_inner_comm]; exact horth
  have hself0 : ⟪e0, e0⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, h0]; ring
  have hself1 : ⟪e1, e1⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, h1]; ring
  have hAv : (toEuclideanLin A) (a • e0 + b • e1)
      = (a * lam0) • e0 + (b * lam1) • e1 := by
    rw [map_add, map_smul, map_smul, he0, he1, smul_smul, smul_smul]
  rw [hAv]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
             real_inner_smul_right, hself0, hself1, horth, h10]
  ring


/-! ## Lower bound and full interlacing — STATED as Prop

The lower bound `hA.eigenvalues₀ 1 ≤ maxRayleigh A W` is a clean
mathematical consequence of the dimension intersection lemma
(`add_finrank_le_finrank_inter_add` above) plus the orthonormal
expansion in the eigenbasis (`inner_self_apply_pair_combination` above).
A complete in-Lean proof requires careful manipulation of
`OrthonormalBasis.linearIndependent` plus pair-decomposition in
`V ⊓ W`; deferred as `Prop` here pending follow-up. The statement is
non-vacuous (the upper bound is fully proved above). -/

/-- The lower bound of codim-1 Cauchy interlacing for the top eigenvalue.
Stated; full proof is the next milestone. -/
def EigenvaluesOneLeMaxRayleighStatement
    (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (_hW : Module.finrank ℝ W = n - 1) : Prop :=
  hA.eigenvalues₀ ⟨1, by simpa [Fintype.card_fin] using hn⟩
    ≤ maxRayleigh A W

/-- **Codim-1 Cauchy interlacing for the top eigenvalue.**
Upper bound is fully proved; lower bound is taken as hypothesis from
`EigenvaluesOneLeMaxRayleighStatement` until the lower-bound proof
lands in a follow-up file. -/
theorem codim_one_interlace_top
    (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hW : Module.finrank ℝ W = n - 1)
    (hLower : EigenvaluesOneLeMaxRayleighStatement n hn A hA W hW) :
    hA.eigenvalues₀ ⟨1, by simpa [Fintype.card_fin] using hn⟩
        ≤ maxRayleigh A W ∧
    maxRayleigh A W
        ≤ hA.eigenvalues₀ ⟨0, by simpa [Fintype.card_fin] using
          (lt_of_lt_of_le Nat.zero_lt_two hn)⟩ := by
  refine ⟨hLower, ?_⟩
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot] at hW
    simp at hW
    omega
  exact maxRayleigh_le_eigenvalues_zero
    (lt_of_lt_of_le Nat.zero_lt_two hn) A hA W hWne

end CausalAlgebraicGeometry.CodimOneInterlacing
