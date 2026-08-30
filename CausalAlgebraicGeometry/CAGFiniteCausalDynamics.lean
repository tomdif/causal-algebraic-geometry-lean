/-
  CAGFiniteCausalDynamics.lean — Effective dynamics on the intrinsic state
  graph of a finite causal algebra.

  The finite-poset development supplies a canonical graph but does not by
  itself select a physical action.  Here we state the nearest-neighbor
  Dirichlet action explicitly and prove its exact finite variation.  The
  resulting Euler–Lagrange operator is the combinatorial graph Laplacian on
  the causal-state partial cube.

  This is a rigorous discrete field equation conditional only on the stated
  effective action.  A continuum limit, physical units, and an observable
  dictionary remain separate hypotheses.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGFiniteCausalGeometry
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.CAGFiniteCausalDynamics

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CausalAlgebra

noncomputable section
open scoped Classical

section FiniteGraph

variable {V : Type*} [Fintype V]

/-- Combinatorial Laplacian written as the sum of outward differences. -/
def graphLaplacian (G : SimpleGraph V) (φ : V → ℝ) (v : V) : ℝ :=
  ∑ w ∈ G.neighborFinset v, (φ v - φ w)

/-- Sourced graph-field residual. -/
def graphFieldResidual (G : SimpleGraph V) (φ source : V → ℝ) (v : V) : ℝ :=
  graphLaplacian G φ v - source v

/-- Star-local Dirichlet energy when the value at `v` is replaced by
`center`, while its neighboring values remain fixed. -/
def localGraphDirichletEnergy (G : SimpleGraph V) (φ source : V → ℝ)
    (v : V) (center : ℝ) : ℝ :=
  (∑ w ∈ G.neighborFinset v, (center - φ w) ^ 2) / 2 - source v * center

/-- Exact finite variation of the graph Dirichlet action.  Its linear term is
the graph Poisson equation, and its quadratic remainder is controlled by the
local graph degree. -/
theorem localGraphDirichletEnergy_variation
    (G : SimpleGraph V) (φ source : V → ℝ) (v : V) (ε : ℝ) :
    localGraphDirichletEnergy G φ source v (φ v + ε) -
        localGraphDirichletEnergy G φ source v (φ v) =
      ε * graphFieldResidual G φ source v +
        (G.degree v : ℝ) * ε ^ 2 / 2 := by
  have hsum :
      (∑ w ∈ G.neighborFinset v, (φ v + ε - φ w) ^ 2) =
        (∑ w ∈ G.neighborFinset v, (φ v - φ w) ^ 2) +
          2 * ε * (∑ w ∈ G.neighborFinset v, (φ v - φ w)) +
          (G.degree v : ℝ) * ε ^ 2 := by
    calc
      (∑ w ∈ G.neighborFinset v, (φ v + ε - φ w) ^ 2) =
          ∑ w ∈ G.neighborFinset v,
            ((φ v - φ w) ^ 2 + 2 * ε * (φ v - φ w) + ε ^ 2) := by
              apply Finset.sum_congr rfl
              intro w _
              ring
      _ = (∑ w ∈ G.neighborFinset v, (φ v - φ w) ^ 2) +
          2 * ε * (∑ w ∈ G.neighborFinset v, (φ v - φ w)) +
          (G.degree v : ℝ) * ε ^ 2 := by
            simp only [Finset.sum_add_distrib, Finset.sum_const,
              nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
            rw [← Finset.mul_sum]
  unfold localGraphDirichletEnergy graphFieldResidual graphLaplacian
  rw [hsum]
  ring

/-- Vanishing of the exact first variation is precisely the sourced graph
Poisson equation. -/
theorem stationary_iff_graphFieldEquation
    (G : SimpleGraph V) (φ source : V → ℝ) (v : V) :
    (∀ ε : ℝ,
      localGraphDirichletEnergy G φ source v (φ v + ε) -
          localGraphDirichletEnergy G φ source v (φ v) -
          (G.degree v : ℝ) * ε ^ 2 / 2 = 0) ↔
      graphLaplacian G φ v = source v := by
  constructor
  · intro h
    have h1 := h 1
    rw [localGraphDirichletEnergy_variation] at h1
    unfold graphFieldResidual at h1
    ring_nf at h1
    linarith
  · intro h ε
    rw [localGraphDirichletEnergy_variation]
    unfold graphFieldResidual
    rw [h]
    ring

/-- Constant fields are graph-harmonic on every finite graph. -/
@[simp]
theorem graphLaplacian_const (G : SimpleGraph V) (c : ℝ) (v : V) :
    graphLaplacian G (fun _ => c) v = 0 := by
  simp [graphLaplacian]

end FiniteGraph

section CausalStates

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Canonical graph Laplacian on the downset states of a finite causal poset. -/
def causalStateLaplacian
    (φ : LowerSet α → ℝ) (s : LowerSet α) : ℝ :=
  graphLaplacian (lowerSetTransitionGraph (α := α)) φ s

/-- The Dirichlet effective action on arbitrary finite causal states has the
intrinsic causal-state graph Laplacian as its exact Euler–Lagrange operator. -/
theorem causalStateDirichlet_stationary_iff
    (φ source : LowerSet α → ℝ) (s : LowerSet α) :
    (∀ ε : ℝ,
      localGraphDirichletEnergy (lowerSetTransitionGraph (α := α))
          φ source s (φ s + ε) -
          localGraphDirichletEnergy (lowerSetTransitionGraph (α := α))
            φ source s (φ s) -
          ((lowerSetTransitionGraph (α := α)).degree s : ℝ) * ε ^ 2 / 2 = 0) ↔
      causalStateLaplacian φ s = source s := by
  exact stationary_iff_graphFieldEquation
    (lowerSetTransitionGraph (α := α)) φ source s

end CausalStates

end
end CausalAlgebraicGeometry.CAGFiniteCausalDynamics
