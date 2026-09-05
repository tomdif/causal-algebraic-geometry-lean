/-
# A low-fragmentation event bound for ordering entropy

If independently sampled profiles have at most K disagreement components
with probability p > 0, then W <= K log 2 - log p. No typical-cluster or
area hypothesis is assumed. This is a finite, deterministic relation among
the exact probabilities; empirical confidence statements are separate.
-/
import CausalAlgebraicGeometry.CAGOrderingClusters

namespace CausalAlgebraicGeometry.CAGClusterStatistics

open C3OrderIdealReduction CAGCompatibilityEntropy CAGMultidimensionalEntropy
open CAGOrderingClusters

noncomputable section
open scoped Classical

/-- A deterministic support bound for the statistical observables. Each
component contains at least one distinct active base point. -/
theorem clusterCount_le_base_size {d m : ℕ} (w : WeakOrderedPair d m) :
    clusterCount w ≤ m ^ d := by
  calc
    clusterCount w ≤ Fintype.card (DisagreementPoint w) :=
      Fintype.card_le_of_surjective componentOf Quot.mk_surjective
    _ ≤ Fintype.card (Fin d → Fin m) := Fintype.card_subtype_le _
    _ = m ^ d := by simp

/-- Exact probability of at most K components under two independent,
uniform trimmed profiles. This is not a sample proportion. -/
def lowClusterProbability (d m K : ℕ) : ℝ :=
  (∑ p : TrimmedProfile d m × TrimmedProfile d m,
    if clusterCount (sortProfiles p) ≤ K then (1 : ℝ) else 0) /
      (trimmedCount d m : ℝ) ^ 2

theorem lowClusterProbability_bounds (d m K : ℕ) (hm : 0 < m) :
    0 ≤ lowClusterProbability d m K ∧ lowClusterProbability d m K ≤ 1 := by
  have hH : (0 : ℝ) < (trimmedCount d m : ℝ) := by
    exact_mod_cast trimmedCount_pos d m hm
  constructor
  · unfold lowClusterProbability
    positivity
  · unfold lowClusterProbability
    apply (div_le_one (sq_pos_of_pos hH)).mpr
    calc
      _ ≤ ∑ _p : TrimmedProfile d m × TrimmedProfile d m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs <;> norm_num
      _ = _ := by simp [Fintype.card_prod, trimmedCount, pow_two]

/-- The success fraction dominates 2^(-K) times the low-fragmentation
probability. This holds even if fragmented configurations exist. -/
theorem lowClusterProbability_le_scaled_success (d m K : ℕ) :
    lowClusterProbability d m K ≤ (2 : ℝ) ^ K *
      ((fullSupportCount d m : ℝ) / (trimmedCount d m : ℝ) ^ 2) := by
  have hcard : Fintype.card (WeakOrderedPair d m) = fullSupportCount d m :=
    (Fintype.card_congr (fullSupportPairEquivWeak d m)).symm
  have hsum := cluster_observable_change_of_ensemble d m
    (fun c => if c ≤ K then (1 : ℝ) else 0)
  have hbound : (∑ w : WeakOrderedPair d m,
      (2 : ℝ) ^ clusterCount w * (if clusterCount w ≤ K then 1 else 0)) ≤
        (2 : ℝ) ^ K * (fullSupportCount d m : ℝ) := by
    calc
      _ ≤ ∑ _w : WeakOrderedPair d m, (2 : ℝ) ^ K := by
        apply Finset.sum_le_sum
        intro w _
        by_cases h : clusterCount w ≤ K
        · simp only [if_pos h, mul_one]
          exact pow_le_pow_right₀ (by norm_num) h
        · simp only [if_neg h, mul_zero]
          positivity
      _ = _ := by simp [hcard, mul_comm]
  unfold lowClusterProbability
  rw [hsum]
  have h := div_le_div_of_nonneg_right hbound
    (sq_nonneg (trimmedCount d m : ℝ))
  simpa only [mul_div_assoc] using h

/-- A usable entropy upper bound from any event of limited fragmentation.
The hypothesis concerns an exact probability, not an estimated one. -/
theorem weakOrderingCost_le_low_cluster_event (d m K : ℕ) (hm : 0 < m)
    (hp : 0 < lowClusterProbability d m K) :
    weakOrderingCost d m ≤ (K : ℝ) * Real.log 2 - Real.log (lowClusterProbability d m K) := by
  have hH : (trimmedCount d m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (trimmedCount_pos d m hm)
  have hQ : (fullSupportCount d m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fullSupportCount_pos d m hm)
  have h := Real.log_le_log hp (lowClusterProbability_le_scaled_success d m K)
  rw [Real.log_mul (by positivity) (div_ne_zero hQ (pow_ne_zero 2 hH)),
    Real.log_div hQ (pow_ne_zero 2 hH), Real.log_pow, Real.log_pow] at h
  unfold weakOrderingCost
  norm_num at h
  linarith

/-- A proven lower bound on the event probability can be substituted.
This is the deterministic interface for a separately justified confidence
bound; the theorem does not validate the sampler or the confidence level. -/
theorem weakOrderingCost_le_of_probability_lower_bound (d m K : ℕ) (hm : 0 < m)
    (p : ℝ) (hp : 0 < p) (hprob : p ≤ lowClusterProbability d m K) :
    weakOrderingCost d m ≤ (K : ℝ) * Real.log 2 - Real.log p := by
  have h := weakOrderingCost_le_low_cluster_event d m K hm (hp.trans_le hprob)
  exact h.trans (sub_le_sub_left (Real.log_le_log hp hprob) _)

/-- A low-fragmentation event need not have probability tending to one:
an area-exponential lower bound already suffices for an area upper bound.
Both hypotheses are explicit and are NOT asserted for CAG here. -/
theorem weakOrderingCost_area_bound_of_event (m K : ℕ) (hm : 0 < m)
    (A B : ℝ) (hK : (K : ℝ) ≤ A * (m : ℝ) ^ 2)
    (hprob : Real.exp (-B * (m : ℝ) ^ 2) ≤ lowClusterProbability 3 m K) :
    weakOrderingCost 3 m ≤ (A * Real.log 2 + B) * (m : ℝ) ^ 2 := by
  have h := weakOrderingCost_le_of_probability_lower_bound 3 m K hm
    (Real.exp (-B * (m : ℝ) ^ 2)) (Real.exp_pos _) hprob
  rw [Real.log_exp] at h
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hk := mul_le_mul_of_nonneg_right hK hlog
  nlinarith

end
end CausalAlgebraicGeometry.CAGClusterStatistics
