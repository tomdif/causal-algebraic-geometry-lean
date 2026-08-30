/-
  CAGRefinementConvergence.lean — Compactness and convergence criteria for
  CAG refinement towers.

  Every normalized directional-curvature sequence takes values in the real
  unit interval, so it has a convergent subsequence without any additional
  hypothesis.  Summable one-step variation upgrades this compactness result
  to convergence of the full sequence and supplies an explicit tail error
  bound.

  Compatible refinements also generate canonical persistent chains from
  every initial event-wall direction.  Pulling tower fields back along these
  chains puts them in one fixed finite-dimensional frame.  Summable pulled-
  back variation then gives a limiting field and the same tail error bound;
  compatible event-labeled fields are proved exactly constant in this frame.

  These theorems construct limits of CAG observables under precise finite-
  variation hypotheses.  They do not yet identify a continuum manifold or
  control field components carried only by directions born after level zero.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGRefinementTower
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Sequences

namespace CausalAlgebraicGeometry.CAGRefinementConvergence

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGDirectionalGeometry
open CausalAlgebraicGeometry.CAGDiscreteConnection
open CausalAlgebraicGeometry.CAGCausalRefinement
open CausalAlgebraicGeometry.CAGRefinementTower
open Filter Set

noncomputable section
open scoped Classical Topology

/-! ## Real curvature-density compactness -/

variable (P : ℕ → Type*)
  [∀ n, PartialOrder (P n)] [∀ n, Fintype (P n)]
variable (step : ∀ n, PastClosedEmbedding (P n) (P (n + 1)))
variable (state : ∀ n, LowerSet (P n))

/-- The rational tower curvature density, embedded in the complete field of
real numbers. -/
def towerCurvatureDensityReal (n : ℕ) : ℝ :=
  (towerCurvatureDensity P state n : ℝ)

theorem towerCurvatureDensityReal_mem_unitInterval (n : ℕ) :
    towerCurvatureDensityReal P state n ∈ Set.Icc (0 : ℝ) 1 := by
  rcases towerCurvatureDensity_mem_unitInterval P state n with ⟨h0, h1⟩
  constructor
  · change 0 ≤ ((towerCurvatureDensity P state n : ℚ) : ℝ)
    exact_mod_cast h0
  · change ((towerCurvatureDensity P state n : ℚ) : ℝ) ≤ 1
    exact_mod_cast h1

/-- Every refinement tower has a subsequence whose normalized directional
curvature converges to a value in the unit interval.  This requires no
regularity assumption on the tower. -/
theorem exists_curvatureDensity_tendsto_subseq :
    ∃ L ∈ Set.Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (towerCurvatureDensityReal P state ∘ φ) atTop (𝓝 L) := by
  exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq
    (towerCurvatureDensityReal_mem_unitInterval P state)

/-- One-step metric variation of normalized tower curvature. -/
def towerCurvatureVariation (n : ℕ) : ℝ :=
  dist (towerCurvatureDensityReal P state n)
    (towerCurvatureDensityReal P state (n + 1))

/-- Finite total curvature variation makes the full density sequence Cauchy. -/
theorem curvatureDensity_cauchy_of_summable_variation
    (hvar : Summable (towerCurvatureVariation P state)) :
    CauchySeq (towerCurvatureDensityReal P state) := by
  apply cauchySeq_of_summable_dist
  simpa [towerCurvatureVariation, Nat.succ_eq_add_one] using hvar

/-- Finite total curvature variation forces convergence, not merely
subsequential convergence, and the limit remains in `[0,1]`. -/
theorem exists_curvatureDensity_limit_of_summable_variation
    (hvar : Summable (towerCurvatureVariation P state)) :
    ∃ L ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (towerCurvatureDensityReal P state) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (curvatureDensity_cauchy_of_summable_variation P state hvar)
  refine ⟨L, ?_, hL⟩
  exact isClosed_Icc.mem_of_tendsto hL
    (Filter.Eventually.of_forall
      (towerCurvatureDensityReal_mem_unitInterval P state))

/-- The unsummed tail variation is an a posteriori error bound for the
limiting curvature density. -/
theorem exists_curvatureDensity_limit_with_tail_bound
    (hvar : Summable (towerCurvatureVariation P state)) :
    ∃ L ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (towerCurvatureDensityReal P state) atTop (𝓝 L) ∧
      ∀ n, dist (towerCurvatureDensityReal P state n) L ≤
        ∑' m : ℕ, towerCurvatureVariation P state (n + m) := by
  obtain ⟨L, hLI, hL⟩ :=
    exists_curvatureDensity_limit_of_summable_variation P state hvar
  refine ⟨L, hLI, hL, fun n => ?_⟩
  simpa [towerCurvatureVariation, Nat.succ_eq_add_one] using
    (dist_le_tsum_dist_of_tendsto hvar hL n)

/-! ## Persistent directions and transported field limits -/

/-- Transport an old event-wall direction through one compatible refinement
step. -/
def extendTowerDirection
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (n : ℕ) (d : EventDirection (state n)) :
    EventDirection (state (n + 1)) :=
  cast (congrArg EventDirection (compatible n).symm)
    (extendDirection (step n) (state n) d)

theorem directionEvent_cast {α : Type*} [PartialOrder α] [Fintype α]
    {s t : LowerSet α} (h : s = t) (d : EventDirection s) :
    directionEvent t (cast (congrArg EventDirection h) d) =
      directionEvent s d := by
  cases h
  rfl

@[simp]
theorem directionEvent_extendTowerDirection
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (n : ℕ) (d : EventDirection (state n)) :
    directionEvent (state (n + 1))
        (extendTowerDirection P step state compatible n d) =
      step n (directionEvent (state n) d) := by
  unfold extendTowerDirection
  rw [directionEvent_cast (compatible n).symm]
  exact directionEvent_extendDirection (step n) (state n) d

/-- The unique refinement chain generated by an initial old direction. -/
def persistentDirection
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (d₀ : EventDirection (state 0)) : ∀ n, EventDirection (state n)
  | 0 => d₀
  | n + 1 => extendTowerDirection P step state compatible n
      (persistentDirection compatible d₀ n)

@[simp]
theorem persistentDirection_zero
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (d₀ : EventDirection (state 0)) :
    persistentDirection P step state compatible d₀ 0 = d₀ := rfl

@[simp]
theorem persistentDirection_succ
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (d₀ : EventDirection (state 0)) (n : ℕ) :
    persistentDirection P step state compatible d₀ (n + 1) =
      extendTowerDirection P step state compatible n
        (persistentDirection P step state compatible d₀ n) := rfl

/-- Pull a tower field back to the initial tangent frame by following every
initial event-wall direction through its persistent refinement chain. -/
def pulledBackTowerField
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (X : ∀ n, DirectionalVector (state n)) (n : ℕ) :
    DirectionalVector (state 0) :=
  fun d₀ => X n (persistentDirection P step state compatible d₀ n)

/-- One-step variation of a tower field after canonical identification of its
old directions with the initial frame. -/
def pulledBackFieldVariation
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (X : ∀ n, DirectionalVector (state n)) (n : ℕ) : ℝ :=
  dist (pulledBackTowerField P step state compatible X n)
    (pulledBackTowerField P step state compatible X (n + 1))

/-- Summable covariant variation on the persistent old frame makes the
transported field Cauchy. -/
theorem pulledBackTowerField_cauchy_of_summable_variation
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (X : ∀ n, DirectionalVector (state n))
    (hvar : Summable (pulledBackFieldVariation P step state compatible X)) :
    CauchySeq (pulledBackTowerField P step state compatible X) := by
  apply cauchySeq_of_summable_dist
  simpa [pulledBackFieldVariation, Nat.succ_eq_add_one] using hvar

/-- A tower field of finite covariant variation converges after transport to
the initial frame. -/
theorem exists_pulledBackTowerField_limit_of_summable_variation
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (X : ∀ n, DirectionalVector (state n))
    (hvar : Summable (pulledBackFieldVariation P step state compatible X)) :
    ∃ Xlim : DirectionalVector (state 0),
      Tendsto (pulledBackTowerField P step state compatible X)
        atTop (𝓝 Xlim) :=
  cauchySeq_tendsto_of_complete
    (pulledBackTowerField_cauchy_of_summable_variation
      P step state compatible X hvar)

/-- The remaining transported variation controls the distance to the limit
field on the persistent initial frame. -/
theorem exists_pulledBackTowerField_limit_with_tail_bound
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (X : ∀ n, DirectionalVector (state n))
    (hvar : Summable (pulledBackFieldVariation P step state compatible X)) :
    ∃ Xlim : DirectionalVector (state 0),
      Tendsto (pulledBackTowerField P step state compatible X)
          atTop (𝓝 Xlim) ∧
      ∀ n, dist (pulledBackTowerField P step state compatible X n) Xlim ≤
        ∑' m : ℕ,
          pulledBackFieldVariation P step state compatible X (n + m) := by
  obtain ⟨Xlim, hXlim⟩ :=
    exists_pulledBackTowerField_limit_of_summable_variation
      P step state compatible X hvar
  refine ⟨Xlim, hXlim, fun n => ?_⟩
  simpa [pulledBackFieldVariation, Nat.succ_eq_add_one] using
    (dist_le_tsum_dist_of_tendsto hvar hXlim n)

/-- Event-labeled tower fields whose labels agree under every causal embedding
are exactly constant after pullback to the initial frame. -/
theorem pulledBackTowerField_eventLabeled_eq_initial
    (compatible : ∀ n, state (n + 1) = extendState (step n) (state n))
    (F : ∀ n, P n → ℝ)
    (hF : ∀ n a, F (n + 1) (step n a) = F n a)
    (n : ℕ) :
    pulledBackTowerField P step state compatible
        (fun k d => F k (directionEvent (state k) d)) n =
      fun d => F 0 (directionEvent (state 0) d) := by
  funext d₀
  induction n with
  | zero => rfl
  | succ n ih =>
      change F (n + 1)
          (directionEvent (state (n + 1))
            (persistentDirection P step state compatible d₀ (n + 1))) = _
      rw [persistentDirection_succ,
        directionEvent_extendTowerDirection, hF]
      exact ih

end
end CausalAlgebraicGeometry.CAGRefinementConvergence
