/-
  CAGBoundaryDynamics.lean — Variational field equation and spectral
  prediction for the CAG boundary geometry.

  Once CAG states are represented by boundary height fields, the minimal
  local quadratic action compatible with height-shift symmetry is the
  nearest-neighbor Dirichlet action.  This file does not claim that the action
  has already been derived from the microscopic BD weights.  It proves the
  consequences of this explicitly stated effective-action hypothesis:

    * Euler–Lagrange equation: 2u_i-u_{i-1}-u_{i+1}=J_i (discrete Poisson);
    * continuum scaling: -(u_{i+1}-2u_i+u_{i-1})/a² = rho_i;
    * exact Fourier symbol: 4 sin²(q/2), giving a falsifiable lattice
      dispersion correction after a physical scale is specified.

  Keeping the effective-action hypothesis explicit prevents these theorems
  from being misreported as an Einstein equation derived from CAG.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGBoundaryGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.CAGBoundaryDynamics

open Real Filter Topology

noncomputable section

/-! ## Local variational principle -/

/-- Local Dirichlet energy around one boundary-height degree of freedom,
including a linear source. -/
def localBoundaryEnergy (left center right source : ℝ) : ℝ :=
  ((center - left) ^ 2 + (right - center) ^ 2) / 2 - source * center

/-- Euler–Lagrange residual of the local boundary action. -/
def boundaryFieldResidual (left center right source : ℝ) : ℝ :=
  2 * center - left - right - source

/-- Exact finite variation formula.  The linear coefficient is the field
equation and the positive quadratic remainder proves stability. -/
theorem localBoundaryEnergy_variation
    (left center right source ε : ℝ) :
    localBoundaryEnergy left (center + ε) right source -
        localBoundaryEnergy left center right source =
      ε * boundaryFieldResidual left center right source + ε ^ 2 := by
  unfold localBoundaryEnergy boundaryFieldResidual
  ring

/-- A local configuration is variationally stationary precisely when it
satisfies the discrete Poisson equation. -/
theorem local_minimum_iff_fieldEquation (left center right source : ℝ) :
    (∀ ε : ℝ,
      localBoundaryEnergy left center right source ≤
        localBoundaryEnergy left (center + ε) right source) ↔
      boundaryFieldResidual left center right source = 0 := by
  constructor
  · intro h
    have hv := h (-(boundaryFieldResidual left center right source) / 2)
    rw [show localBoundaryEnergy left
        (center + (-(boundaryFieldResidual left center right source) / 2)) right source =
        localBoundaryEnergy left center right source +
          (-(boundaryFieldResidual left center right source) / 2) *
            boundaryFieldResidual left center right source +
          (-(boundaryFieldResidual left center right source) / 2) ^ 2 by
      linarith [localBoundaryEnergy_variation left center right source
        (-(boundaryFieldResidual left center right source) / 2)]] at hv
    nlinarith [sq_nonneg (boundaryFieldResidual left center right source)]
  · intro heq ε
    have hv := localBoundaryEnergy_variation left center right source ε
    rw [heq, mul_zero, zero_add] at hv
    nlinarith [sq_nonneg ε]

/-- With lattice spacing `a` and a continuum-scaled source `a² rho`, the
same equation is the centered finite-difference Poisson equation. -/
theorem fieldEquation_scaled (a left center right ρ : ℝ) (ha : a ≠ 0) :
    boundaryFieldResidual left center right (a ^ 2 * ρ) = 0 ↔
      -((right - 2 * center + left) / a ^ 2) = ρ := by
  unfold boundaryFieldResidual
  constructor <;> intro h
  · field_simp [ha]
    linarith
  · field_simp [ha] at h
    linarith

/-! ## Exact Fourier symbol: a falsifiable spectral signature -/

/-- Eigenvalue of the negative nearest-neighbor lattice Laplacian. -/
def latticeDispersion (q : ℝ) : ℝ := 2 - 2 * Real.cos q

/-- The lattice symbol has the canonical sine-squared form. -/
theorem latticeDispersion_eq (q : ℝ) :
    latticeDispersion q = 4 * Real.sin (q / 2) ^ 2 := by
  unfold latticeDispersion
  rw [show q = 2 * (q / 2) by ring, Real.cos_two_mul]
  ring_nf
  rw [Real.sin_sq]
  ring

theorem latticeDispersion_nonneg (q : ℝ) : 0 ≤ latticeDispersion q := by
  rw [latticeDispersion_eq]
  positivity

/-- A cosine mode is an exact eigenmode of the centered discrete Laplacian. -/
theorem cosine_mode_residual (θ q : ℝ) :
    2 * Real.cos θ - Real.cos (θ - q) - Real.cos (θ + q) =
      latticeDispersion q * Real.cos θ := by
  unfold latticeDispersion
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- Conditional physical dispersion relation.  If the effective boundary
field has wave speed `c` and lattice spacing `a`, its squared frequency is
`(c/a)² 4 sin²(q/2)`.  This differs from the continuum `c²k²` away from the
long-wavelength limit and is therefore, once `a` is fixed independently, a
falsifiable prediction rather than a fitted identity. -/
def predictedOmegaSq (c a q : ℝ) : ℝ :=
  (c / a) ^ 2 * latticeDispersion q

theorem predictedOmegaSq_formula (c a q : ℝ) :
    predictedOmegaSq c a q = (c / a) ^ 2 * 4 * Real.sin (q / 2) ^ 2 := by
  rw [predictedOmegaSq, latticeDispersion_eq]
  ring

end
end CausalAlgebraicGeometry.CAGBoundaryDynamics
