/-
  CauchyInterlacing.lean — Rayleigh quotient and Courant-Fischer / Cauchy
  interlacing scaffolding for real symmetric matrices.

  STATUS: Layer A (Rayleigh quotient + Rayleigh-Ritz upper bound for the
  largest eigenvalue) is fully proved. Layers B (general Courant-Fischer
  min-max formula) and C (rank-r Cauchy interlacing) are stated as
  `Prop`-valued goals (`CourantFischerStatement`, `CauchyInterlacingStatement`)
  to be discharged in follow-up work. No sorry, no axiom.

  Convention: Mathlib's `Matrix.IsHermitian.eigenvalues` is sorted in
  DECREASING order via `LinearMap.IsSymmetric.eigenvalues_antitone`, so
  `hA.eigenvalues 0` is the largest eigenvalue.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.CauchyInterlacing

open scoped InnerProductSpace
open Matrix Module Submodule

variable {n : ℕ}

/-! ## Layer A — Rayleigh quotient -/

/-- The Rayleigh quotient of a real symmetric matrix `A` at a vector `v`,
defined as `⟪v, A v⟫ / ⟪v, v⟫`. Returns `0` when `v = 0`. -/
noncomputable def rayleigh (A : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪v, (toEuclideanLin A) v⟫_ℝ / ‖v‖ ^ 2

/-- Rayleigh quotient evaluated at `0` is `0` (by convention). -/
@[simp] lemma rayleigh_zero (A : Matrix (Fin n) (Fin n) ℝ) :
    rayleigh A (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  simp [rayleigh]

/-- Scaling-invariance of the Rayleigh quotient. -/
lemma rayleigh_smul (A : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : c ≠ 0) :
    rayleigh A (c • v) = rayleigh A v := by
  by_cases hv : v = 0
  · simp [hv]
  unfold rayleigh
  rw [map_smul, real_inner_smul_left, inner_smul_right, norm_smul, mul_pow]
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  have habs : ‖c‖ ^ 2 = c * c := by
    rw [Real.norm_eq_abs, sq_abs, sq]
  rw [habs]
  field_simp

/-- For nonzero `v`, the Rayleigh quotient equals
`⟪v, A v⟫ / ‖v‖²`. -/
lemma rayleigh_eq_div (A : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    rayleigh A v = ⟪v, (toEuclideanLin A) v⟫_ℝ / ‖v‖ ^ 2 := rfl

/-- For an `IsHermitian` matrix `A` and an eigenvector `e_i`
of the spectral basis, the Rayleigh quotient equals the corresponding
eigenvalue. -/
lemma rayleigh_eigenvectorBasis
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i : Fin n) :
    rayleigh A (hA.eigenvectorBasis i) = hA.eigenvalues i := by
  classical
  have horth : ‖(hA.eigenvectorBasis i : EuclideanSpace ℝ (Fin n))‖ = 1 :=
    hA.eigenvectorBasis.orthonormal.1 i
  have hmul : (toEuclideanLin A) (hA.eigenvectorBasis i)
      = (hA.eigenvalues i) • (hA.eigenvectorBasis i : EuclideanSpace ℝ (Fin n)) := by
    -- `toEuclideanLin A v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp 2 v)`; using
    -- `mulVec_eigenvectorBasis` we get the eigenvalue scaling.
    have := hA.mulVec_eigenvectorBasis i
    -- Convert via toEuclideanLin
    apply (WithLp.linearEquiv 2 ℝ _).injective
    simp [Matrix.toEuclideanLin, WithLp.linearEquiv, this, Matrix.toLin'_apply]
  rw [rayleigh, hmul, inner_smul_right]
  have h1 : ⟪(hA.eigenvectorBasis i : EuclideanSpace ℝ (Fin n)),
              (hA.eigenvectorBasis i : EuclideanSpace ℝ (Fin n))⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, horth, one_pow]
  rw [h1, mul_one, horth, one_pow, div_one]

/-- The Rayleigh quotient as a function on the unit sphere
attains its supremum (compactness of the sphere in finite dimension). -/
lemma exists_isMaxOn_rayleigh_sphere [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ v₀ : EuclideanSpace ℝ (Fin n), ‖v₀‖ = 1 ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → rayleigh A w ≤ rayleigh A v₀ := by
  classical
  -- Continuity of the inner-product expression on a finite-dim sphere.
  have hcont : Continuous fun v : EuclideanSpace ℝ (Fin n) =>
      ⟪v, (toEuclideanLin A) v⟫_ℝ := by
    have h1 : Continuous (fun v : EuclideanSpace ℝ (Fin n) => v) := continuous_id
    have h2 : Continuous (fun v : EuclideanSpace ℝ (Fin n) => (toEuclideanLin A) v) :=
      (toEuclideanLin A).continuous_of_finiteDimensional
    exact (continuous_inner.comp (h1.prodMk h2))
  have hSph : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_sphere _ _
  -- Pick any unit vector to witness nonemptiness.
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty (Fin n)›
    refine ⟨EuclideanSpace.single i (1 : ℝ), ?_⟩
    simp [Metric.mem_sphere, EuclideanSpace.norm_single]
  obtain ⟨v₀, hv₀mem, hmax⟩ :=
    hSph.exists_isMaxOn hne hcont.continuousOn
  refine ⟨v₀, ?_, ?_⟩
  · simpa [Metric.mem_sphere] using hv₀mem
  · intro w hw
    have hwmem : w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_sphere] using hw
    have h := hmax hwmem
    have hnv₀ : ‖v₀‖ = 1 := by simpa [Metric.mem_sphere] using hv₀mem
    -- `rayleigh A v = ⟪v, A v⟫ / ‖v‖² = ⟪v, A v⟫` on the unit sphere.
    have hrv : rayleigh A v₀ = ⟪v₀, (toEuclideanLin A) v₀⟫_ℝ := by
      simp [rayleigh, hnv₀]
    have hrw : rayleigh A w = ⟪w, (toEuclideanLin A) w⟫_ℝ := by
      simp [rayleigh, hw]
    rw [hrv, hrw]
    exact h

/-! ## Bridge: top eigenvalue equals max Rayleigh on the unit sphere

This is the Rayleigh-Ritz half of Courant-Fischer (the `k = 0` case in
Mathlib's descending convention). -/

/-- Rayleigh-Ritz: for a Hermitian (symmetric) matrix `A`, the top
eigenvalue `hA.eigenvalues 0` is achieved by the corresponding
eigenvector, which has unit norm. -/
lemma rayleigh_top_eigenvalue_attained [Nonempty (Fin n)]
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧
      ∃ i : Fin n, rayleigh A v = hA.eigenvalues i := by
  classical
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  refine ⟨hA.eigenvectorBasis i, ?_, i, ?_⟩
  · exact hA.eigenvectorBasis.orthonormal.1 _
  · exact rayleigh_eigenvectorBasis A hA i

/-! ## Layer B (statement) — Courant-Fischer min-max formula -/

/-- The set of `k`-dimensional submodules of `EuclideanSpace ℝ (Fin n)`. -/
def subspacesOfDim (k : ℕ) : Set (Submodule ℝ (EuclideanSpace ℝ (Fin n))) :=
  { V | Module.finrank ℝ V = k }

/-- The min Rayleigh quotient over nonzero vectors of a submodule `V`. -/
noncomputable def minRayleigh (A : Matrix (Fin n) (Fin n) ℝ)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⨅ v : { v : V // (v : EuclideanSpace ℝ (Fin n)) ≠ 0 }, rayleigh A (v.1 : _)

/-- The max Rayleigh quotient over nonzero vectors of a submodule `V`. -/
noncomputable def maxRayleigh (A : Matrix (Fin n) (Fin n) ℝ)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⨆ v : { v : V // (v : EuclideanSpace ℝ (Fin n)) ≠ 0 }, rayleigh A (v.1 : _)

/-- **Courant-Fischer (statement)**: the `k`th eigenvalue of a real
symmetric matrix `A` (in Mathlib's descending order, so the `k`th-largest)
equals the supremum over `(k+1)`-dimensional subspaces of the infimum of
the Rayleigh quotient on that subspace.

This is left as a Prop to be discharged in follow-up work. -/
def CourantFischerStatement (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) : Prop :=
  ∀ k : Fin n,
    hA.eigenvalues k =
      ⨆ V ∈ subspacesOfDim (k.val + 1), minRayleigh A V

/-- **Dual Courant-Fischer (statement)**: the same eigenvalue is also
the infimum, over `(n-k)`-dimensional subspaces, of the supremum
of the Rayleigh quotient. -/
def CourantFischerDualStatement (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) : Prop :=
  ∀ k : Fin n,
    hA.eigenvalues k =
      ⨅ V ∈ subspacesOfDim (n - k.val), maxRayleigh A V

/-! ## Layer C (statement) — rank-r Cauchy interlacing -/

/-- **Rank-r Cauchy interlacing (statement)** in Mathlib's descending
convention. For `A B : Matrix (Fin n) (Fin n) ℝ` both Hermitian with
`rank (B - A) ≤ r`, we have for every `k : Fin n`:

  * if `k.val + r < n` then `B.eigenvalues ⟨k.val + r, _⟩ ≤ A.eigenvalues k`;
  * if `r ≤ k.val` then `A.eigenvalues k ≤ B.eigenvalues ⟨k.val - r, _⟩`.

This is left as a Prop to be discharged in follow-up work using the
Courant-Fischer formula above and the dimension-intersection bound
`dim (V ∩ ker (B - A)) ≥ dim V − r`. -/
def CauchyInterlacingStatement
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (r : ℕ) (hR : (B - A).rank ≤ r) : Prop :=
  ∀ k : Fin n,
    (∀ h : k.val + r < n,
        hB.eigenvalues ⟨k.val + r, h⟩ ≤ hA.eigenvalues k) ∧
    (∀ h : r ≤ k.val,
        hA.eigenvalues k ≤ hB.eigenvalues ⟨k.val - r, by
          have : k.val - r ≤ k.val := Nat.sub_le _ _
          exact lt_of_le_of_lt this k.isLt⟩)

/-! ## Sanity checks: trivial cases of the statements above -/

/-- The rank-0 (i.e. `B = A`) case of Cauchy interlacing is trivially true. -/
lemma cauchyInterlacing_rank_zero
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    CauchyInterlacingStatement A A hA hA 0 (by simp) := by
  intro k
  refine ⟨?_, ?_⟩
  · intro h
    have heq : (⟨k.val + 0, h⟩ : Fin n) = k := by
      apply Fin.ext; simp
    rw [heq]
  · intro _
    have hlt : k.val - 0 < n := by rw [Nat.sub_zero]; exact k.isLt
    have heq : (⟨k.val - 0, hlt⟩ : Fin n) = k := by
      apply Fin.ext; simp
    rw [heq]

end CausalAlgebraicGeometry.CauchyInterlacing
