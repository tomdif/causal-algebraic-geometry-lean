/-
  CAGScalingLimit.lean — A controlled continuum-scaling family for CAG.

  The downset-state graph of an n-event causal chain is identified exactly
  with the path graph on n+1 vertices.  This supplies a canonical coordinate
  for that family: the number of realized events.  With an independently
  chosen lattice spacing h, the intrinsic graph Laplacian becomes the
  centered finite-difference operator.

  The final theorems certify the continuum comparison on quartic test fields:
  the scaled graph operator equals minus the continuum second derivative plus
  an explicit O(h^2) error.  This is a genuine consistency theorem for a
  controlled family, not a claim that arbitrary causal algebras canonically
  determine h or a continuum manifold.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGCubicalComplex
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Archimedean

namespace CausalAlgebraicGeometry.CAGScalingLimit

open CausalAlgebraicGeometry.CAGFiniteCausalGeometry
open CausalAlgebraicGeometry.CAGFiniteCausalDynamics
open CausalAlgebraicGeometry.CAGTransitionGeometry

noncomputable section
open scoped Classical

/-! ## Finite causal chains are exactly path-state geometries -/

/-- Prefix/downset containing precisely the first `k` events of an `n`-event
causal chain. -/
def chainState (n : ℕ) (k : Fin (n + 1)) : LowerSet (Fin n) where
  carrier := {i | i.val < k.val}
  lower' := by
    intro a b hab hb
    change a.val < k.val at hb
    change b.val < k.val
    exact lt_of_le_of_lt (Fin.mk_le_mk.mp hab) hb

@[simp]
theorem mem_chainState_iff {n : ℕ} {k : Fin (n + 1)} {i : Fin n} :
    i ∈ chainState n k ↔ i.val < k.val :=
  Iff.rfl

theorem chainState_injective (n : ℕ) :
    Function.Injective (chainState n) := by
  intro k l hkl
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hkn : k.val < n := by omega
    let i : Fin n := ⟨k.val, hkn⟩
    have hm : i ∈ chainState n k ↔ i ∈ chainState n l := by rw [hkl]
    simp [mem_chainState_iff, i, hlt] at hm
  · have hln : l.val < n := by omega
    let i : Fin n := ⟨l.val, hln⟩
    have hm : i ∈ chainState n k ↔ i ∈ chainState n l := by rw [hkl]
    simp [mem_chainState_iff, i, hgt] at hm

theorem chainState_surjective (n : ℕ) :
    Function.Surjective (chainState n) := by
  intro s
  rcases s.lower.eq_univ_or_Iio with htop | ⟨a, ha⟩
  · let k : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    refine ⟨k, ?_⟩
    apply LowerSet.ext
    ext i
    simp [chainState, k, htop]
  · let k : Fin (n + 1) := ⟨a.val, lt_trans a.isLt (Nat.lt_succ_self n)⟩
    refine ⟨k, ?_⟩
    apply LowerSet.ext
    ext i
    change i.val < a.val ↔ i ∈ (s : Set (Fin n))
    rw [ha]
    rfl

/-- Coordinate equivalence between event count `0,...,n` and all downsets of
the n-event causal chain. -/
def chainStateEquiv (n : ℕ) : Fin (n + 1) ≃ LowerSet (Fin n) :=
  Equiv.ofBijective (chainState n)
    ⟨chainState_injective n, chainState_surjective n⟩

@[simp]
theorem chainStateEquiv_apply (n : ℕ) (k : Fin (n + 1)) :
    chainStateEquiv n k = chainState n k := rfl

/-- Event-wall distance between chain states is the ordinary integer distance
between their event counts. -/
theorem chainState_distance (n : ℕ) (k l : Fin (n + 1)) :
    lowerSetDistance (chainState n k) (chainState n l) =
      Nat.dist k.val l.val := by
  have hk : lowerSetCode (chainState n k) = unaryHeightCode k := by
    funext i
    simp [lowerSetCode, unaryHeightCode, mem_chainState_iff]
  have hl : lowerSetCode (chainState n l) = unaryHeightCode l := by
    funext i
    simp [lowerSetCode, unaryHeightCode, mem_chainState_iff]
  unfold lowerSetDistance
  rw [hk, hl]
  exact hammingDist_unaryHeightCode k l

theorem chainState_adj_iff_pathGraph_adj (n : ℕ) (k l : Fin (n + 1)) :
    (lowerSetTransitionGraph (α := Fin n)).Adj
        (chainState n k) (chainState n l) ↔
      (SimpleGraph.pathGraph (n + 1)).Adj k l := by
  change lowerSetDistance (chainState n k) (chainState n l) = 1 ↔ _
  rw [chainState_distance, SimpleGraph.pathGraph_adj]
  unfold Nat.dist
  omega

/-- **CHAIN/PATH IDENTIFICATION.** The intrinsic state graph of the finite
causal chain is graph-isomorphic to a uniform finite path. -/
def chainStateGraphIso (n : ℕ) :
    SimpleGraph.pathGraph (n + 1) ≃g
      lowerSetTransitionGraph (α := Fin n) where
  toEquiv := chainStateEquiv n
  map_rel_iff' := by
    intro k l
    exact chainState_adj_iff_pathGraph_adj n k l

/-! ## Exact graph Laplacian in chain coordinates -/

/-- Predecessor of an interior path coordinate. -/
def chainLeft {n : ℕ} (k : Fin (n + 1)) (hk0 : 0 < k.val) : Fin (n + 1) :=
  ⟨k.val - 1, by omega⟩

/-- Successor of an interior path coordinate. -/
def chainRight {n : ℕ} (k : Fin (n + 1)) (hkn : k.val < n) : Fin (n + 1) :=
  ⟨k.val + 1, by omega⟩

@[simp]
theorem chainLeft_val {n : ℕ} (k : Fin (n + 1)) (hk0 : 0 < k.val) :
    (chainLeft k hk0).val = k.val - 1 := rfl

@[simp]
theorem chainRight_val {n : ℕ} (k : Fin (n + 1)) (hkn : k.val < n) :
    (chainRight k hkn).val = k.val + 1 := rfl

theorem pathGraph_neighborFinset_interior {n : ℕ} (k : Fin (n + 1))
    (hk0 : 0 < k.val) (hkn : k.val < n) :
    (SimpleGraph.pathGraph (n + 1)).neighborFinset k =
      {chainLeft k hk0, chainRight k hkn} := by
  ext j
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right
      apply Fin.ext
      exact h.symm
    · left
      apply Fin.ext
      dsimp [chainLeft]
      omega
  · rintro (h | h)
    · right
      have hv := congrArg Fin.val h
      dsimp [chainLeft] at hv
      omega
    · left
      have hv := congrArg Fin.val h
      exact hv.symm

/-- The two path neighbors of an interior chain coordinate are distinct. -/
theorem chainLeft_ne_chainRight {n : ℕ} (k : Fin (n + 1))
    (hk0 : 0 < k.val) (hkn : k.val < n) :
    chainLeft k hk0 ≠ chainRight k hkn := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [chainLeft, chainRight] at hv
  omega

/-- Exact centered-difference formula on the ordinary path graph. -/
theorem graphLaplacian_pathGraph_interior {n : ℕ} (u : Fin (n + 1) → ℝ)
    (k : Fin (n + 1)) (hk0 : 0 < k.val) (hkn : k.val < n) :
    graphLaplacian (SimpleGraph.pathGraph (n + 1)) u k =
      2 * u k - u (chainLeft k hk0) - u (chainRight k hkn) := by
  unfold graphLaplacian
  rw [pathGraph_neighborFinset_interior k hk0 hkn]
  have hne := chainLeft_ne_chainRight k hk0 hkn
  simp [hne]
  ring

/-- The neighbor set of an interior CAG chain state consists exactly of the
states with one fewer and one more realized causal event. -/
theorem chainState_neighborFinset_interior {n : ℕ} (k : Fin (n + 1))
    (hk0 : 0 < k.val) (hkn : k.val < n) :
    (lowerSetTransitionGraph (α := Fin n)).neighborFinset (chainState n k) =
      {chainState n (chainLeft k hk0),
        chainState n (chainRight k hkn)} := by
  ext s
  obtain ⟨j, rfl⟩ := chainState_surjective n s
  rw [SimpleGraph.mem_neighborFinset,
    chainState_adj_iff_pathGraph_adj,
    ← SimpleGraph.mem_neighborFinset,
    pathGraph_neighborFinset_interior k hk0 hkn]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · left
      exact congrArg (chainState n) h
    · right
      exact congrArg (chainState n) h
  · rintro (h | h)
    · left
      exact chainState_injective n h
    · right
      exact chainState_injective n h

/-- **INTRINSIC FINITE-DIFFERENCE THEOREM.** On the causal-chain family, the
CAG state-graph Laplacian is exactly the centered second-difference numerator. -/
theorem graphLaplacian_chainState_interior {n : ℕ}
    (φ : LowerSet (Fin n) → ℝ) (k : Fin (n + 1))
    (hk0 : 0 < k.val) (hkn : k.val < n) :
    graphLaplacian (lowerSetTransitionGraph (α := Fin n)) φ (chainState n k) =
      2 * φ (chainState n k) - φ (chainState n (chainLeft k hk0)) -
        φ (chainState n (chainRight k hkn)) := by
  unfold graphLaplacian
  rw [chainState_neighborFinset_interior k hk0 hkn]
  have hne : chainState n (chainLeft k hk0) ≠
      chainState n (chainRight k hkn) :=
    (chainState_injective n).ne (chainLeft_ne_chainRight k hk0 hkn)
  simp [hne]
  ring

/-! ## Independent scale and continuum consistency -/

/-- Physical coordinate assigned to a chain state after specifying a lattice
spacing `h`.  The order alone does not choose `h`; it is explicit data. -/
def chainCoordinate {n : ℕ} (h : ℝ) (k : Fin (n + 1)) : ℝ :=
  h * k.val

theorem chainCoordinate_left {n : ℕ} (h : ℝ) (k : Fin (n + 1))
    (hk0 : 0 < k.val) :
    chainCoordinate h (chainLeft k hk0) = chainCoordinate h k - h := by
  unfold chainCoordinate chainLeft
  rw [Nat.cast_sub (by omega : 1 ≤ k.val)]
  norm_num
  ring

theorem chainCoordinate_right {n : ℕ} (h : ℝ) (k : Fin (n + 1))
    (hkn : k.val < n) :
    chainCoordinate h (chainRight k hkn) = chainCoordinate h k + h := by
  unfold chainCoordinate chainRight
  push_cast
  ring

/-- Sample a continuum field on every downset state of the finite causal
chain, using the exact event-count coordinate. -/
def chainSample (n : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    LowerSet (Fin n) → ℝ :=
  fun s => f (chainCoordinate h ((chainStateEquiv n).symm s))

@[simp]
theorem chainSample_chainState (n : ℕ) (h : ℝ) (f : ℝ → ℝ)
    (k : Fin (n + 1)) :
    chainSample n h f (chainState n k) = f (chainCoordinate h k) := by
  unfold chainSample
  change f (chainCoordinate h ((chainStateEquiv n).symm (chainStateEquiv n k))) = _
  rw [Equiv.symm_apply_apply]

/-- Exact sampled-field formula before division by the lattice area. -/
theorem graphLaplacian_chainSample_interior (n : ℕ) (h : ℝ) (f : ℝ → ℝ)
    (k : Fin (n + 1)) (hk0 : 0 < k.val) (hkn : k.val < n) :
    graphLaplacian (lowerSetTransitionGraph (α := Fin n))
        (chainSample n h f) (chainState n k) =
      2 * f (chainCoordinate h k) - f (chainCoordinate h k - h) -
        f (chainCoordinate h k + h) := by
  rw [graphLaplacian_chainState_interior (chainSample n h f) k hk0 hkn]
  simp only [chainSample_chainState]
  rw [chainCoordinate_left h k hk0, chainCoordinate_right h k hkn]

/-- Scaled intrinsic graph Laplacian for the causal-chain family. -/
def scaledChainLaplacian (n : ℕ) (h : ℝ) (f : ℝ → ℝ)
    (k : Fin (n + 1)) : ℝ :=
  graphLaplacian (lowerSetTransitionGraph (α := Fin n))
      (chainSample n h f) (chainState n k) / h ^ 2

/-- The scaled CAG operator is exactly the negative centered second
difference at every interior state. -/
theorem scaledChainLaplacian_eq_centeredDifference
    (n : ℕ) (h : ℝ) (f : ℝ → ℝ) (k : Fin (n + 1))
    (hk0 : 0 < k.val) (hkn : k.val < n) :
    scaledChainLaplacian n h f k =
      (2 * f (chainCoordinate h k) - f (chainCoordinate h k - h) -
        f (chainCoordinate h k + h)) / h ^ 2 := by
  unfold scaledChainLaplacian
  rw [graphLaplacian_chainSample_interior n h f k hk0 hkn]

/-- Quartic test field, sufficiently rich to expose the leading truncation
error of the centered operator. -/
def quarticField (A B C D E x : ℝ) : ℝ :=
  A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E

/-- Exact continuum second derivative of `quarticField`. -/
def quarticSecondDerivative (A B C x : ℝ) : ℝ :=
  12 * A * x ^ 2 + 6 * B * x + 2 * C

/-- Algebraic consistency formula for the negative centered difference on a
quartic: the entire truncation error is `-2 A h²`. -/
theorem quartic_centeredDifference_exact
    (A B C D E x h : ℝ) (hh : h ≠ 0) :
    (2 * quarticField A B C D E x -
          quarticField A B C D E (x - h) -
          quarticField A B C D E (x + h)) / h ^ 2 =
      -quarticSecondDerivative A B C x - 2 * A * h ^ 2 := by
  unfold quarticField quarticSecondDerivative
  field_simp [hh]
  ring

/-- **CONTROLLED CAG/CONTINUUM ERROR THEOREM.** For every interior state of
every finite causal chain, the scaled intrinsic CAG Laplacian on a sampled
quartic differs from minus the continuum second derivative by exactly
`-2 A h²`, uniformly in the chain length and position. -/
theorem scaledChainLaplacian_quartic_exact
    (n : ℕ) (A B C D E h : ℝ) (hh : h ≠ 0)
    (k : Fin (n + 1)) (hk0 : 0 < k.val) (hkn : k.val < n) :
    scaledChainLaplacian n h (quarticField A B C D E) k =
      -quarticSecondDerivative A B C (chainCoordinate h k) -
        2 * A * h ^ 2 := by
  rw [scaledChainLaplacian_eq_centeredDifference n h _ k hk0 hkn]
  exact quartic_centeredDifference_exact A B C D E (chainCoordinate h k) h hh

/-- Uniform absolute consistency error on the causal-chain family. -/
theorem scaledChainLaplacian_quartic_error
    (n : ℕ) (A B C D E h : ℝ) (hh : h ≠ 0)
    (k : Fin (n + 1)) (hk0 : 0 < k.val) (hkn : k.val < n) :
    |scaledChainLaplacian n h (quarticField A B C D E) k +
        quarticSecondDerivative A B C (chainCoordinate h k)| =
      2 * |A| * h ^ 2 := by
  rw [scaledChainLaplacian_quartic_exact n A B C D E h hh k hk0 hkn]
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  rw [show -quarticSecondDerivative A B C (chainCoordinate h k) -
      2 * A * h ^ 2 + quarticSecondDerivative A B C (chainCoordinate h k) =
      (-2) * A * h ^ 2 by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hh2]
  norm_num

/-- The uniform error coefficient tends to zero quadratically as the external
mesh scale tends to zero. -/
theorem quarticConsistencyError_tendsto_zero (A : ℝ) :
    Filter.Tendsto (fun h : ℝ => 2 * |A| * h ^ 2) (nhds 0) (nhds 0) := by
  have hcont : ContinuousAt (fun h : ℝ => 2 * |A| * h ^ 2) 0 := by
    fun_prop
  simpa using hcont.tendsto

/-- Uniform mesh on a physical interval of independently specified length
`L`, using the `n` transition steps of the n-event causal chain. -/
def chainMesh (L : ℝ) (n : ℕ) : ℝ :=
  L / (n : ℝ)

/-- For nonzero chain length, the final causal state is placed exactly at the
specified physical endpoint `L`. -/
theorem chainCoordinate_terminal (L : ℝ) (n : ℕ) (hn : n ≠ 0) :
    chainCoordinate (chainMesh L n) (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = L := by
  unfold chainCoordinate chainMesh
  field_simp [Nat.cast_ne_zero.mpr hn]

/-- The externally scaled chain meshes converge to zero as the causal chains
grow. -/
theorem chainMesh_tendsto_zero (L : ℝ) :
    Filter.Tendsto (chainMesh L) Filter.atTop (nhds 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat L

/-- Along the fixed-length causal-chain family, the certified quartic
consistency error converges to zero. -/
theorem quarticChainFamily_error_tendsto_zero (A L : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => 2 * |A| * (chainMesh L n) ^ 2)
      Filter.atTop (nhds 0) := by
  exact (quarticConsistencyError_tendsto_zero A).comp
    (chainMesh_tendsto_zero L)

end
end CausalAlgebraicGeometry.CAGScalingLimit
