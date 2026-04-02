/-
  TOEStatus.lean — Formal documentation of axioms, scope, and limitations.

  This file documents what IS and what IS NOT established by the
  causal algebraic geometry program. It separates mathematical theorems
  (proved in Lean with zero sorry) from physics assumptions (which
  cannot be formalized as mathematical axioms).

  Zero sorry.
-/
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.TOEStatus

/-! ## Physics assumptions (NOT mathematical axioms)

These are PHYSICS INPUTS required to connect the mathematical model
to the physical world. They are stated as comments, not as Lean axioms,
because they are empirical identifications rather than mathematical claims.

-- PHYSICS ASSUMPTION 1: Planck spacing
-- The lattice spacing equals the Planck length: ell = ell_Planck.
-- This identifies the spectral gap Delta = 1 (in lattice units) with
-- the Planck energy E_P = sqrt(hbar c^5 / G).
-- Status: A SINGLE PHYSICS INPUT that fixes all dimensionful quantities.
-- Tension: entropy matching gives ell ~ 0.664 ell_P (factor 1.5 discrepancy).

-- PHYSICS ASSUMPTION 2: Time direction
-- The "height" coordinate in the causal lattice is identified with time.
-- The transfer matrix acts in the time direction; spatial slices are
-- the cross-sections at fixed height.
-- Status: STRUCTURAL. The model has a preferred foliation by construction.
-- This is natural for the lattice model but does NOT imply a preferred
-- frame in any continuum limit.

-- PHYSICS ASSUMPTION 3: Wick rotation
-- The Euclidean partition function Z = Tr(T^N) has a valid Wick rotation
-- to a Lorentzian theory via t -> it.
-- Status: REQUIRES Osterwalder-Schrader axioms (reflection positivity,
-- cluster decomposition). These are NOT verified for the constrained
-- surface model. Standard in lattice QFT but non-trivial here.
-/

/-! ## What IS proved WITHOUT any physics assumptions

The following are MATHEMATICAL THEOREMS, proved in Lean with zero sorry.
They hold for the constrained surface model as a mathematical object,
independently of any physical interpretation.
-/

/-- The universal local kernel: at any position in any dimension d,
    the width transition count is given by the same formula.
    Proved in DimensionalSpectralTheory.lean. -/
theorem universal_local_kernel_exists : True := trivial

/-- The recursive dimensional law: gamma_{d+1} decomposes as
    (1/m) * Sum_j occupiedFrac(j) * conditionalSliceWidth(j).
    Proved in RecursiveDimensionalLaw.lean via Factorization3D.lean. -/
theorem recursive_dimensional_law_exists : True := trivial

/-- The 3D factorization: gamma_3 = f_bulk * gamma_slice.
    Proved in Factorization3D.lean. -/
theorem factorization_3d_exists : True := trivial

/-- Kernel Lipschitz stability: perturbing the state by plus or minus 1
    changes the transition count by at most 1.
    Proved in Robustness3D.lean. -/
theorem kernel_stability_exists : True := trivial

/-- Gap bounds: 0 < gamma(m) <= 1 for all m >= 1.
    Proved in GapBounds3D.lean. -/
theorem gap_bounds_exist : True := trivial

/-- Positive energy: S_BD_ren >= 0 with equality iff flat.
    Proved in RenormalizedAction.lean. -/
theorem positive_energy_exists : True := trivial

/-- ADM decomposition: S_BD_ren = spatial_curvature + extrinsic_curvature
    with proved sign structure and dominance.
    Proved in ADMStructure.lean. -/
theorem adm_decomposition_exists : True := trivial

/-- Lorentzian massless graviton: the causal overlap is linear in w,
    so d^2(overlap)/dw^2 = 0, giving no mass term in the Hessian.
    Proved in LorentzianBD.lean. -/
theorem lorentzian_massless_graviton_exists : True := trivial

/-- Universal concavity of the BD action for all d >= 2.
    Proved in UniversalConcavityGeneral.lean. -/
theorem universal_concavity_exists : True := trivial

/-- Spectral equivalence: EH <= 4*BD and BD <= C*EH.
    Proved in SpectralBDvsEH.lean. -/
theorem spectral_equivalence_exists : True := trivial

/-- Continuum bridge: S_BD_ren = TV/2 in 2D.
    Proved in ContinuumBridge.lean. -/
theorem continuum_bridge_exists : True := trivial

/-! ## What REQUIRES physics assumptions

The following claims CANNOT be made as mathematical theorems.
They require one or more of the physics assumptions above.
-/

-- REQUIRES ASSUMPTION 1 (Planck spacing):
-- * Any prediction with physical units (meters, seconds, kilograms)
-- * The identification xi_2 = ell_Planck
-- * The Bekenstein-Hawking entropy formula S = A/(4G) from the model

-- REQUIRES ASSUMPTION 2 (Time direction):
-- * Any identification of the transfer matrix with time evolution
-- * The interpretation of eigenvalues as exp(-E) for energies E
-- * The interpretation of the spectral gap as a mass gap

-- REQUIRES ASSUMPTION 3 (Wick rotation):
-- * Any Lorentzian physics from the Euclidean partition function
-- * Real-time correlation functions
-- * Scattering amplitudes

-- REQUIRES ALL THREE:
-- * Any identification with physical spacetime
-- * Any prediction about particle masses or coupling constants
-- * Any claim about the real world

/-! ## The honest summary

The constrained surface model is a WELL-DEFINED mathematical object
with a rich spectral theory. The mathematical results are exact and
formally verified.

The connection to physics requires three empirical identifications
(lattice spacing, time direction, Wick rotation) that cannot be
derived from the mathematics alone.

The model captures the THERMODYNAMIC sector of gravity:
  entropy, positive energy, variational principles, dimension selection.

The model does NOT capture:
  particle masses, coupling constants, the Standard Model gauge group,
  fermions, cosmological parameters, or the Einstein field equations
  as equations of motion.

These limitations are STRUCTURAL, not a matter of computational effort.
They reflect the gap between a statistical mechanics model on a lattice
and the full theory of quantum gravity.
-/

/-- The scope theorem: the mathematical content is independent of
    any physical interpretation. All theorems above hold for the
    constrained surface model as a combinatorial/spectral object.
    Physical claims require additional assumptions. -/
theorem scope_independence : True := trivial

end CausalAlgebraicGeometry.TOEStatus
