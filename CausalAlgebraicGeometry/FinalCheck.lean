/-
  FinalCheck.lean — Small, explicit verification surface for CAG.

  This file mirrors the useful part of the FLT repository's verification
  architecture: a short list of challenge-facing theorem names, followed by
  kernel-axiom reports for each endpoint.  It intentionally imports no
  experimental RH target.
-/
import CausalAlgebraicGeometry.CSpecActualSheaf
import CausalAlgebraicGeometry.CSpecRingSheaf
import CausalAlgebraicGeometry.ChamberGaloisBridge
import CausalAlgebraicGeometry.ChamberGenericFamily
import CausalAlgebraicGeometry.ChamberFrobenius
import CausalAlgebraicGeometry.CSpecChamberRoots
import CausalAlgebraicGeometry.ChamberGaloisD4
import CausalAlgebraicGeometry.CSpecChamberRootsCounterexample
import CausalAlgebraicGeometry.DimensionLawComplete
import CausalAlgebraicGeometry.GrowthRateIs16
import CausalAlgebraicGeometry.C3AsymptoticClosure
import CausalAlgebraicGeometry.CAGSolidPartitionVolume
import CausalAlgebraicGeometry.CAGCompatibilityEntropy
import CausalAlgebraicGeometry.CAGOrderingClusters
import CausalAlgebraicGeometry.CAGClusterStatistics
import CausalAlgebraicGeometry.CAGRefinementConvergence

namespace CausalAlgebraicGeometry.FinalCheck

open CausalAlgebra

/-- Challenge-facing endpoint for the all-dimensional finite-size law. -/
theorem checked_dimension_law (d m : ℕ) (hd : 2 ≤ d) :
    2 ^ (m ^ d / (d * m + 1)) ≤
        DimensionLaw.numConvexDim d m ∧
      DimensionLaw.numConvexDim d m ≤ 16 ^ (m ^ (d - 1)) :=
  DimensionLawComplete.dimension_law_explicit d m hd

/-- Challenge-facing endpoint for the exact two-dimensional growth rate. -/
theorem checked_growth_constant :
    GrowthConstant.neg_log_subadditive.lim = -Real.log 16 :=
  GrowthRateIs16.growth_constant_eq_neg_log_sixteen

/-- Challenge-facing endpoint for unconditional cubic entropy factorization. -/
theorem checked_c3_entropy_factorization :
    Filter.Tendsto
      (fun m : ℕ =>
        (2 * Real.log (DimensionLaw.downsetCountDim 3 m : ℝ) -
          Real.log (DimensionLaw.numConvexDim 3 m : ℝ)) / (m : ℝ) ^ 2)
      Filter.atTop (nhds 0) :=
  C3AsymptoticClosure.convex_entropy_gap_tendsto_zero

/-- Every ambient dimension at least three has two-boundary entropy
factorization, including the boxed solid-partition case in dimension four. -/
theorem checked_multidimensional_entropy_factorization (r : ℕ) :
    Filter.Tendsto
      (fun m : ℕ =>
        (2 * Real.log (DimensionLaw.downsetCountDim (r + 3) m : ℝ) -
          Real.log (DimensionLaw.numConvexDim (r + 3) m : ℝ)) /
            (m : ℝ) ^ (r + 2)) Filter.atTop (nhds 0) :=
  CAGMultidimensionalEntropy.convex_entropy_gap_tendsto_zero r

/-- The actual fixed-volume solid-partition count is recovered from a
sufficiently large box.  No asymptotic constant is assumed. -/
theorem checked_solid_partition_volume_bridge (n m : ℕ) (hnm : n < m) :
    CAGSolidPartitionVolume.solidPartitionCount n =
      CAGSolidPartitionVolume.boxedPartitionCount 3 m n :=
  CAGSolidPartitionVolume.solidPartitionCount_eq_boxed n m hnm

/-- Some volume coefficient retains boxed entropy up to a polynomial factor;
the theorem deliberately does not identify that volume. -/
theorem checked_solid_partition_large_coefficient (m : ℕ) :
    ∃ n, n ≤ m ^ 4 ∧ DimensionLaw.downsetCountDim 4 m ≤
      (m ^ 4 + 1) * CAGSolidPartitionVolume.boxedPartitionCount 3 m n :=
  CAGSolidPartitionVolume.exists_large_volume_coefficient 3 m

/-- The compatibility deficit is a uniform-counting surprisal and splits
into two nonnegative costs. This does not identify a gravitational entropy. -/
theorem checked_compatibility_entropy_decomposition (d m : ℕ) (hm : 0 < m) :
    CAGCompatibilityEntropy.compatibilityDeficit d m =
        -Real.log (CAGCompatibilityEntropy.compatibilityProbability d m) ∧
      0 ≤ CAGCompatibilityEntropy.heightTrimmingCost d m ∧
      0 ≤ CAGCompatibilityEntropy.weakOrderingCost d m ∧
      CAGCompatibilityEntropy.compatibilityDeficit d m =
        CAGCompatibilityEntropy.heightTrimmingCost d m +
          CAGCompatibilityEntropy.weakOrderingCost d m :=
  ⟨CAGCompatibilityEntropy.compatibilityDeficit_eq_neg_log_probability d m hm,
    CAGCompatibilityEntropy.compatibility_entropy_decomposition d m hm⟩

/-- Only the height-trimming contribution has the proved sharp area upper
bound; the complete compatibility area law remains an open target. -/
theorem checked_height_trimming_area_bound (m : ℕ) (hm : 0 < m) :
    CAGCompatibilityEntropy.heightTrimmingCost 3 m ≤
      2 * (m : ℝ) ^ 2 * Real.log 16 :=
  CAGCompatibilityEntropy.heightTrimmingCost_area_upper 1 m hm

/-- An equivalence of two open upper-bound targets, not a proof of either. -/
theorem checked_compatibility_area_reduction :
    CAGCompatibilityEntropy.AreaUpperBoundFour
        (CAGCompatibilityEntropy.compatibilityDeficit 3) ↔
      CAGCompatibilityEntropy.AreaUpperBoundFour
        (CAGCompatibilityEntropy.weakOrderingCost 3) :=
  CAGCompatibilityEntropy.area_upper_bound_iff_weak_ordering

/-- Exact cluster partition function for the residual ordering cost. -/
theorem checked_ordering_cluster_identity (d m : ℕ) (hm : 0 < m) :
    CAGCompatibilityEntropy.trimmedCount d m ^ 2 =
        (∑ w : C3OrderIdealReduction.WeakOrderedPair d m,
          2 ^ CAGOrderingClusters.clusterCount w) ∧
      CAGCompatibilityEntropy.weakOrderingCost d m =
        Real.log (CAGOrderingClusters.clusterExponentialMoment d m) :=
  ⟨CAGOrderingClusters.trimmed_square_eq_cluster_sum d m,
    CAGOrderingClusters.weakOrderingCost_eq_log_cluster_moment d m hm⟩

/-- Ownership constraints are generated by immediate causal comparisons;
this is not a proof that entropy itself is an additive local functional. -/
theorem checked_ordering_cluster_locality {d m : ℕ}
    (w : C3OrderIdealReduction.WeakOrderedPair d m)
    (f : CAGOrderingClusters.DisagreementPoint w → Bool) :
    (∀ a b, CAGOrderingClusters.Overlap w a b → f a = f b) ↔
      (∀ a b, a.val ⋖ b.val → w.lower a.val < w.upper b.val → f a = f b) :=
  CAGOrderingClusters.overlap_invariance_iff_cover_invariance w f

/-- The two different ensembles give rigorous lower and upper mean-cluster
bounds. No area-scale control of either mean is assumed or concluded. -/
theorem checked_ordering_cluster_mean_bounds (d m : ℕ) (hm : 0 < m) :
    Real.log 2 * CAGOrderingClusters.orderedMeanClusters d m ≤
        CAGCompatibilityEntropy.weakOrderingCost d m ∧
      CAGCompatibilityEntropy.weakOrderingCost d m ≤
        Real.log 2 * CAGOrderingClusters.independentMeanClusters d m :=
  CAGOrderingClusters.weakOrderingCost_mean_cluster_bounds d m hm

/-- The deterministic range used by the statistical experiment. -/
theorem checked_cluster_statistic_range {d m : ℕ} (w : C3OrderIdealReduction.WeakOrderedPair d m) :
    CAGOrderingClusters.clusterCount w ≤ m ^ d :=
  CAGClusterStatistics.clusterCount_le_base_size w

/-- A lower bound on an exact low-fragmentation probability bounds entropy.
The sampling implementation and confidence guarantee are not asserted here. -/
theorem checked_low_cluster_entropy_bound (d m K : ℕ) (hm : 0 < m)
    (p : ℝ) (hp : 0 < p) (hprob : p ≤ CAGClusterStatistics.lowClusterProbability d m K) :
    CAGCompatibilityEntropy.weakOrderingCost d m ≤ (K : ℝ) * Real.log 2 - Real.log p :=
  CAGClusterStatistics.weakOrderingCost_le_of_probability_lower_bound d m K hm p hp hprob

/-- A conditional sufficient criterion, not an unconditional area theorem. -/
theorem checked_cluster_area_event_criterion (m K : ℕ) (hm : 0 < m)
    (A B : ℝ) (hK : (K : ℝ) ≤ A * (m : ℝ) ^ 2)
    (hprob : Real.exp (-B * (m : ℝ) ^ 2) ≤ CAGClusterStatistics.lowClusterProbability 3 m K) :
    CAGCompatibilityEntropy.weakOrderingCost 3 m ≤ (A * Real.log 2 + B) * (m : ℝ) ^ 2 :=
  CAGClusterStatistics.weakOrderingCost_area_bound_of_event m K hm A B hK hprob

/-- Challenge-facing endpoint certifying that CSpec carries an actual
Mathlib sheaf rather than only a bespoke locality predicate. -/
theorem checked_cspec_sheaf {k : Type*} [Field k] (C : CAlg k) :
    (CSpecActualSheaf.causalCornerSheaf C).presheaf.IsSheaf :=
  CSpecActualSheaf.causalCornerSheaf_isSheaf C

/-- Challenge-facing endpoint for rational structural deflation. -/
theorem checked_rational_chamber_factorization (d : ℕ) (hd : 3 ≤ d) :
    (Polynomial.X - Polynomial.C (ChamberGaloisBridge.qTopZero d)) *
        ChamberGaloisBridge.qResidualChamberPolynomial d =
      ChamberGaloisBridge.qChamberPolynomial d :=
  ChamberGaloisBridge.qChamber_factorization d hd

/-- Challenge-facing endpoint for faithfulness of the actual splitting-field
Galois action.  Full symmetric surjectivity remains the conjecture. -/
theorem checked_chamber_galois_faithful (d : ℕ) :
    Function.Injective (ChamberGaloisBridge.chamberGaloisActionHom d) :=
  ChamberGaloisBridge.chamberGaloisAction_faithful d

/-- The causal-corner structure sheaf retains its noncommutative ring
operations and unital restriction maps. -/
theorem checked_cspec_ring_sheaf {k : Type*} [Field k] (C : CAlg k) :
    (CSpecRingSheaf.causalCornerRingSheaf C).presheaf.IsSheaf :=
  CSpecRingSheaf.causalCornerRingSheaf_isSheaf C

/-- The generic parameter family recovers the rational chamber polynomial at
the arithmetic specialization `δ = d`. -/
theorem checked_generic_chamber_specialization (d : ℕ) :
    ChamberGenericFamily.parameterChamberPolynomial d (d : ℚ) =
      ChamberGaloisBridge.qChamberPolynomial d :=
  ChamberGenericFamily.parameterChamberPolynomial_specializes_to_q d

/-- A concrete replayable finite-field seed: the `d = 4` residual chamber
model has certified factor-degree pattern `[2]` after reduction modulo 11. -/
theorem checked_q4_frobenius_seed :
    Nonempty (ChamberFrobenius.FrobeniusFactorCertificate 4 11 [2]) :=
  ⟨ChamberFrobenius.q4Mod11Certificate⟩

/-- The local chamber-root assignment over CSpec is an actual sheaf. -/
theorem checked_cspec_chamber_root_sheaf {k : Type*} [Field k] (C : CAlg k) :
    (CSpecChamberRoots.causalChamberRootSheaf C).presheaf.IsSheaf :=
  CSpecChamberRoots.causalChamberRootSheaf_isSheaf C

/-- Every local chamber splitting-field action is faithful. -/
theorem checked_local_chamber_galois_faithful {k : Type*} [Field k]
    (C : CAlg k) (P : CSpecActualSheaf.CSpecTop C) :
    Function.Injective (CSpecChamberRoots.localChamberGaloisActionHom C P) :=
  CSpecChamberRoots.localChamberGaloisAction_faithful C P

/-- The first nontrivial chamber-symmetry case is a theorem: the residual
quadratic in dimension four has its full symmetric Galois action. -/
theorem checked_full_chamber_galois_four :
    ChamberGaloisBridge.HasFullChamberGaloisGroup 4 :=
  ChamberGaloisD4.hasFullChamberGaloisGroup_four

noncomputable local instance checkedChamberRootFourDecidableEq :
    DecidableEq (ChamberGaloisBridge.ChamberRoot 4) := Classical.decEq _

/-- The mod-11 factor pattern is realized by an actual characteristic-zero
Galois element in the first certified case. -/
theorem checked_q4_frobenius_cycle_bridge :
    ∃ σ : (ChamberGaloisBridge.qResidualChamberPolynomial 4).Gal,
      (ChamberGaloisBridge.chamberGaloisActionHom 4 σ).cycleType =
        ([2].filter fun degree => degree ≠ 1) :=
  ChamberGaloisD4.q4Mod11Certificate_realizes_cycle_pattern

/-- Root fibres are canonically constant on each local-dimension stratum. -/
theorem checked_chamber_root_stratified_constant
    {k : Type*} [Field k] (C : CAlg k) (n : ℕ)
    (P Q : CSpecActualSheaf.CSpecTop C)
    (hP : CSpecChamberRoots.localChamberDimension C P = n)
    (hQ : CSpecChamberRoots.localChamberDimension C Q = n) :
    Nonempty
      (CSpecChamberRoots.localChamberRootFiber C P ≃
        CSpecChamberRoots.localChamberRootFiber C Q) :=
  CSpecChamberRoots.chamberRootFiber_constant_on_dimension_stratum
    C n P Q hP hQ

/-- Unstratified local constancy is false for general causal spectra; the
two-element chain is an explicit kernel-checked counterexample. -/
theorem checked_unstratified_root_local_system_fails :
    ¬ CSpecChamberRoots.ChamberRootLocalSystemStatement
      CSpecChamberRootsCounterexample.chainTwo :=
  CSpecChamberRootsCounterexample.not_chamberRootLocalSystemStatement_chainTwo

/-! These guarded reports make any future dependency change a build failure. -/

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_dimension_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_dimension_law

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_growth_constant' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_growth_constant

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_c3_entropy_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_c3_entropy_factorization

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_multidimensional_entropy_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_multidimensional_entropy_factorization

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_solid_partition_volume_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_solid_partition_volume_bridge

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_solid_partition_large_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_solid_partition_large_coefficient

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_compatibility_entropy_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_compatibility_entropy_decomposition

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_height_trimming_area_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_height_trimming_area_bound

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_compatibility_area_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_compatibility_area_reduction

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_ordering_cluster_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_ordering_cluster_identity

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_ordering_cluster_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_ordering_cluster_locality

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_ordering_cluster_mean_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_ordering_cluster_mean_bounds

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_cluster_statistic_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_cluster_statistic_range

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_low_cluster_entropy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_low_cluster_entropy_bound

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_cluster_area_event_criterion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_cluster_area_event_criterion

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_cspec_sheaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_cspec_sheaf

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_rational_chamber_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_rational_chamber_factorization

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_chamber_galois_faithful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_chamber_galois_faithful

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_cspec_ring_sheaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_cspec_ring_sheaf

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_generic_chamber_specialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_generic_chamber_specialization

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_q4_frobenius_seed' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_q4_frobenius_seed

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_cspec_chamber_root_sheaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_cspec_chamber_root_sheaf

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_local_chamber_galois_faithful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_local_chamber_galois_faithful

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_full_chamber_galois_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_full_chamber_galois_four

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_q4_frobenius_cycle_bridge' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_q4_frobenius_cycle_bridge

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_chamber_root_stratified_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_chamber_root_stratified_constant

/-- info: 'CausalAlgebraicGeometry.FinalCheck.checked_unstratified_root_local_system_fails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_unstratified_root_local_system_fails

/-- info: 'CausalAlgebraicGeometry.CAGRefinementConvergence.exists_curvatureDensity_tendsto_subseq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CAGRefinementConvergence.exists_curvatureDensity_tendsto_subseq

end CausalAlgebraicGeometry.FinalCheck
