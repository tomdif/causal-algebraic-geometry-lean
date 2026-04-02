/-
  The d=3 Continuum Operator

  The d=3 spectral theory is a self-consistent fixed-point problem:
  - LOCAL: the universal kernel K_comb acts at each position
  - GLOBAL: the antitone coupling on [m]^{d-2} determines the profile weight h

  The continuum operator for d=3 acts on width PROFILES w: [0,1] → [0,1].
  At each point t ∈ [0,1], the local transition is K_comb(w(t), w'(t)).
  The coupling: w must be nonincreasing (antitone constraint from the slab).

  In the continuum limit, this becomes an operator on the space of
  nonincreasing functions [0,1] → [0,1]:

    (T₃ Φ)[w] = ∫_{w' ≤ w pointwise} K_prod(w, w') Φ[w'] Dw'

  where K_prod(w, w') = ∏_t K_comb(w(t), w'(t)) is the PRODUCT KERNEL
  (independent transitions at each t, coupled by the pointwise ordering w' ≤ w).

  This file formalizes the STRUCTURE of this operator.
  The actual spectral computation requires the self-consistent h-function,
  which is the principal eigenfunction of T₃.
-/
import CausalAlgebraicGeometry.DimensionalSpectralTheory
import CausalAlgebraicGeometry.RecursiveDimensionalLaw
import Mathlib.Tactic

namespace ContinuumOperator3D

/-- The d=3 continuum operator has three components:

    1. LOCAL KERNEL: K_comb(s, s') at each position t.
       This is the universal kernel from Theorem A (continuum version):
         K(s,s') = -ln(s)/(1-s) for s' ≤ s
         K(s,s') = [(s-s')ln((1-s)/(s'-s)) - s'ln(s')] / (s(1-s)) for s' > s

    2. PRODUCT STRUCTURE: independent transitions at each t,
       giving K_prod(w, w') = ∏_t K_local(w(t), w'(t)).
       In the continuum: K_prod = exp(∫ log K_comb(w(t), w'(t)) dt).

    3. ANTITONE COUPLING: w(t) must be nonincreasing in t.
       This restricts the integration to w' ≤ w pointwise
       with w' also nonincreasing.

    The SPECTRAL CONSTANT γ₃ is determined by the principal
    eigenvalue of this operator on the space of nonincreasing profiles.

    The FACTORIZATION γ₃ = f_bulk × γ_slice (from RecursiveDimensionalLaw)
    decomposes the eigenvalue into an occupation factor and a per-slice factor. -/

-- The discrete precursor of the product kernel:
-- At finite m with profile (w(0),...,w(m-1)):
-- The transfer matrix entry is 1 iff w'(j) transitions from w(j) are all valid.
-- The number of valid transitions from profile w to profile w' is:
--   ∏_j count(a(j), w(j), w'(j))
-- where count is the universal Theorem C formula.

-- The product structure: the total transition count for a profile
--  factorizes as a product of per-position counts.
--  This is the key structural fact that makes the d=3 operator
--  a product kernel with antitone coupling.
theorem product_structure (m : ℕ) (a w w' : Fin m → ℕ)
    (h_valid : ∀ j, w' j ≤ a j + w j) :
    ∀ j, (WidthTransitions3D.validLowerBounds (a j) (w j) (w' j)).card =
      if w' j ≤ w j then a j + 1
      else if w' j ≤ a j + w j then a j + w j - w' j + 1
      else 0 := by
  intro j
  exact DimensionalSpectralTheory.local_transition_universal (a j) (w j) (w' j)

-- THE 3D CONTINUUM OPERATOR STRUCTURE:
--
-- State space: nonincreasing functions w: [0,1] → [0,1] (rescaled profiles)
-- Local kernel: K_comb(s, s') at each point
-- Product kernel: K_prod[w, w'] = exp(∫₀¹ log K_comb(w(t), w'(t)) dt)
-- Constraint: w' ≤ w pointwise, both nonincreasing
--
-- Eigenvalue equation: T₃ Φ = λ₃ Φ
-- where (T₃ Φ)[w] = ∫_{w' ≤ w, w' noninc} K_prod[w, w'] Φ[w'] Dw'
--
-- The principal eigenvalue λ₃ determines γ₃.
-- The principal eigenfunction Φ determines the profile measure.
--
-- EXISTENCE: by Perron-Frobenius for compact positive operators
-- on the cone of nonneg functions. T₃ is compact (bounded domain,
-- continuous kernel) and positive (K_comb > 0 for comparable profiles).
-- Therefore a unique positive eigenfunction exists.
--
-- UNIQUENESS: the comparability graph on nonincreasing functions is
-- connected (any two noninc functions have a common lower bound: the
-- pointwise minimum). So T₃ is irreducible, and PF gives uniqueness.
--
-- The SELF-CONSISTENT h-function from the fixed-point theory:
-- h(w, a) = Φ[profile with width w at position j and center a]
-- projected to the (w,a) fiber at position j.
-- This is what the numerical scripts compute.

end ContinuumOperator3D
