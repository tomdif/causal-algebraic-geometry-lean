/-
# Boundary entropy factorization in every dimension at least three

The deterministic quantization and shift maps in the cubic argument work in
every base dimension.  Threshold layers bound a thin profile by a tuple of
lower-dimensional downsets.  Combining this with the proved dimension law
gives an explicit subleading loss in every fixed dimension.

In particular, boxed solid partitions (downsets of `[m]^4`) satisfy
`log (#convex subsets of [m]^4) = 2 log (#downsets of [m]^4) + o(m^3)`.
This is a comparison of two counts, not an evaluation of either entropy
constant and not an asymptotic formula for solid partitions of fixed volume.
-/
import CausalAlgebraicGeometry.C3AsymptoticClosure
import CausalAlgebraicGeometry.DimensionLawComplete

namespace CausalAlgebraicGeometry.CAGMultidimensionalEntropy

open C3BarrierLowerBound C3ShiftCompression C3MultiscaleCompression
open C3AsymptoticClosure FullSupportLowerBound DimensionLaw
open DimensionLawComplete SlabBijection
open Real Filter Topology

noncomputable section
open scoped Classical

/-- Strictly separated boundary pairs on a base of dimension `d`. -/
def fullSupportCount (d m : ℕ) : ℕ := Fintype.card (FullSupportPair d m)

theorem fullSupportCount_pos (d m : ℕ) (hm : 0 < m) :
    0 < fullSupportCount d m := by
  let p : FullSupportPair d m :=
    ⟨fun _ => 0, fun _ => m, fun _ => le_rfl,
      fun _ _ _ => le_rfl, fun _ _ _ => le_rfl, fun _ => hm⟩
  exact Fintype.card_pos_iff.mpr ⟨p⟩

theorem fullSupportCount_le_downset_square (d m : ℕ) :
    fullSupportCount d m ≤ downsetCountDim (d + 1) m ^ 2 := by
  rw [← card_antitoneProfile_eq_downsetCount, pow_two, ← Fintype.card_prod]
  exact Fintype.card_le_of_injective profilePairOfFullSupport
    profilePairOfFullSupport_injective

/-- The tube compression estimate is independent of base dimension. -/
theorem tube_square_le_fullSupport_mul_thin (d m k : ℕ)
    (b : (Fin d → Fin m) → ℕ) (hb : ∀ f, b f < m) :
    Fintype.card (LimitTube d m b k) ^ 2 ≤
      fullSupportCount d m * (Fintype.card (ThinProfile d m k) *
        Fintype.card (ThinProfile d m (k + 1))) := by
  have hl := tube_card_le_below_mul_thin (d := d) (m := m) (k := k) b
  have hu := tube_card_le_above_mul_thin (d := d) (m := m) (k := k) b hb
  calc
    Fintype.card (LimitTube d m b k) ^ 2 ≤
        (Fintype.card (BelowBarrier d m b) * Fintype.card (ThinProfile d m k)) *
          (Fintype.card (AboveBarrier d m b) *
            Fintype.card (ThinProfile d m (k + 1))) := by
      simpa only [pow_two] using Nat.mul_le_mul hl hu
    _ = (Fintype.card (BelowBarrier d m b) * Fintype.card (AboveBarrier d m b)) *
        (Fintype.card (ThinProfile d m k) *
          Fintype.card (ThinProfile d m (k + 1))) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (barrier_product_le_fullSupport d m b)

/-- Finite multiscale compression in arbitrary dimension, retaining the
actual thin-profile counts instead of assuming a surface entropy formula. -/
theorem downset_square_le_multiscale (d m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    downsetCountDim (d + 1) m ^ 2 ≤
      4 * Fintype.card (ThinProfile d m (m / (k + 1))) ^ 2 *
        (fullSupportCount d m * (Fintype.card (ThinProfile d m k) *
          Fintype.card (ThinProfile d m (k + 1)))) := by
  let N := Fintype.card (AntitoneProfile d m)
  let C := Fintype.card (ThinProfile d m (m / (k + 1)))
  have hC : 0 < C := Fintype.card_pos_iff.mpr inferInstance
  have hCN : C ≤ N :=
    thinProfile_card_le_antitoneProfile d m (m / (k + 1)) (Nat.div_le_self _ _)
  have hN : N ≤ 2 * C * (N / C) := le_two_mul_floor_average N C hC hCN
  obtain ⟨q, hq⟩ := exists_large_coarseFiber d m k
  have hft : Fintype.card (CoarseFiber k q) ≤
      Fintype.card (LimitTube d m (coarseBarrier k q) k) :=
    Fintype.card_le_of_injective (coarseFiberToTube hm hk q)
      (coarseFiberToTube_injective hm hk q)
  have hA := (Nat.pow_le_pow_left (hq.trans hft) 2).trans
    (tube_square_le_fullSupport_mul_thin d m k (coarseBarrier k q)
      (coarseBarrier_lt hm q))
  rw [← card_antitoneProfile_eq_downsetCount]
  calc
    N ^ 2 ≤ (2 * C * (N / C)) ^ 2 := Nat.pow_le_pow_left hN 2
    _ = 4 * C ^ 2 * (N / C) ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hA

/-- Elementary thin-profile bound in base dimension `r+2`. -/
theorem thinProfile_card_le_sixteen_pow (r m k : ℕ) :
    Fintype.card (ThinProfile (r + 2) m k) ≤ 16 ^ (m ^ (r + 1) * k) := by
  calc
    Fintype.card (ThinProfile (r + 2) m k) ≤
        downsetCountDim (r + 2) m ^ k := thinProfile_card_le_downset_pow _ _ _
    _ ≤ numConvexDim (r + 2) m ^ k :=
      Nat.pow_le_pow_left (downsetCountDim_le_numConvexDim _ _) _
    _ ≤ (16 ^ (m ^ (r + 1))) ^ k :=
      Nat.pow_le_pow_left (numConvexDim_upper_indexed r m) _
    _ = _ := by rw [pow_mul]

/-- Explicit finite error at any positive quantization scale. -/
theorem downset_square_le_power_correction (r m k : ℕ)
    (hm : 0 < m) (hk : 0 < k) :
    downsetCountDim (r + 3) m ^ 2 ≤
      fullSupportCount (r + 2) m *
        16 ^ (m ^ r * (1 + 2 * (m * (m / (k + 1))) + m * k + m * (k + 1))) := by
  have hmain := downset_square_le_multiscale (r + 2) m k hm hk
  have hcoarse := thinProfile_card_le_sixteen_pow r m (m / (k + 1))
  have hlo := thinProfile_card_le_sixteen_pow r m k
  have hup := thinProfile_card_le_sixteen_pow r m (k + 1)
  have hone : 1 ≤ m ^ r := Nat.one_le_pow _ _ hm
  have hfour : 4 ≤ 16 ^ (m ^ r) := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (16 : ℕ)) hone
    norm_num at h ⊢
    omega
  calc
    downsetCountDim (r + 3) m ^ 2 ≤
        4 * Fintype.card (ThinProfile (r + 2) m (m / (k + 1))) ^ 2 *
          (fullSupportCount (r + 2) m * (Fintype.card (ThinProfile (r + 2) m k) *
            Fintype.card (ThinProfile (r + 2) m (k + 1)))) := hmain
    _ ≤ 16 ^ (m ^ r) * (16 ^ (m ^ (r + 1) * (m / (k + 1)))) ^ 2 *
        (fullSupportCount (r + 2) m *
          (16 ^ (m ^ (r + 1) * k) * 16 ^ (m ^ (r + 1) * (k + 1)))) :=
      Nat.mul_le_mul (Nat.mul_le_mul hfour (Nat.pow_le_pow_left hcoarse 2))
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul hlo hup))
    _ = _ := by
      rw [← pow_mul]
      simp only [← pow_add]
      rw [show m ^ (r + 1) = m ^ r * m by rw [pow_succ]]
      ring

/-- The all-dimensional exponent reuses the proved cubic square-root scale. -/
def entropyErrorExponent (r m : ℕ) : ℕ := m ^ r * correctionExponent m

theorem downset_square_le_entropy_correction (r m : ℕ) (hm : 0 < m) :
    downsetCountDim (r + 3) m ^ 2 ≤
      fullSupportCount (r + 2) m * 16 ^ entropyErrorExponent r m := by
  simpa [entropyErrorExponent, correctionExponent, Nat.add_assoc] using
    downset_square_le_power_correction r m (Nat.sqrt m + 1) hm (by omega)

theorem entropyErrorExponent_bound (r m : ℕ) :
    entropyErrorExponent r m ≤ m ^ r * (1 + 4 * m * Nat.sqrt m + 3 * m) :=
  Nat.mul_le_mul_left _ (correctionExponent_le m)

theorem normalized_entropyError_tendsto_zero (r : ℕ) :
    Tendsto (fun m : ℕ => (entropyErrorExponent r m : ℝ) / (m : ℝ) ^ (r + 2))
      atTop (𝓝 0) := by
  apply tendsto_correctionExponent_div_sq.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  simp only [entropyErrorExponent, Nat.cast_mul, Nat.cast_pow, pow_add]
  field_simp

/-- Quantitative entropy sandwich for strictly separated boundaries. -/
theorem pair_entropy_gap_bounds (r m : ℕ) (hm : 0 < m) :
    0 ≤ 2 * Real.log (downsetCountDim (r + 3) m : ℝ) -
        Real.log (fullSupportCount (r + 2) m : ℝ) ∧
      2 * Real.log (downsetCountDim (r + 3) m : ℝ) -
        Real.log (fullSupportCount (r + 2) m : ℝ) ≤
          (entropyErrorExponent r m : ℝ) * Real.log 16 := by
  have hQ : (0 : ℝ) < (fullSupportCount (r + 2) m : ℝ) := by
    exact_mod_cast fullSupportCount_pos (r + 2) m hm
  have hupper := fullSupportCount_le_downset_square (r + 2) m
  have hupperR : (fullSupportCount (r + 2) m : ℝ) ≤
      (downsetCountDim (r + 3) m : ℝ) ^ 2 := by exact_mod_cast hupper
  have hDsq : (0 : ℝ) < (downsetCountDim (r + 3) m : ℝ) ^ 2 :=
    hQ.trans_le hupperR
  constructor
  · have h := Real.log_le_log hQ hupperR
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  · have h := Real.log_le_log hDsq
      (show (downsetCountDim (r + 3) m : ℝ) ^ 2 ≤
          (fullSupportCount (r + 2) m : ℝ) * 16 ^ entropyErrorExponent r m by
        exact_mod_cast downset_square_le_entropy_correction r m hm)
    rw [Real.log_pow, Real.log_mul (ne_of_gt hQ) (by positivity), Real.log_pow] at h
    norm_num at h
    linarith

theorem pair_entropy_gap_tendsto_zero (r : ℕ) :
    Tendsto (fun m : ℕ =>
      (2 * Real.log (downsetCountDim (r + 3) m : ℝ) -
        Real.log (fullSupportCount (r + 2) m : ℝ)) / (m : ℝ) ^ (r + 2))
      atTop (𝓝 0) := by
  have hlim := (normalized_entropyError_tendsto_zero r).mul_const (Real.log 16)
  simp only [zero_mul] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact div_nonneg (pair_entropy_gap_bounds r m (by omega)).1 (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have h := div_le_div_of_nonneg_right
      (pair_entropy_gap_bounds r m (by omega)).2 (by positivity : 0 ≤ (m : ℝ) ^ (r + 2))
    convert h using 1
    ring

/-- Explicit error bound for the convex-set entropy, before taking limits. -/
theorem convex_entropy_gap_bounds (r m : ℕ) (hm : 0 < m) :
    0 ≤ 2 * Real.log (downsetCountDim (r + 3) m : ℝ) -
        Real.log (numConvexDim (r + 3) m : ℝ) ∧
      2 * Real.log (downsetCountDim (r + 3) m : ℝ) -
        Real.log (numConvexDim (r + 3) m : ℝ) ≤
          (entropyErrorExponent r m : ℝ) * Real.log 16 := by
  refine ⟨sub_nonneg.mpr (log_sandwich (r + 3) m).2, ?_⟩
  have hQ : (0 : ℝ) < (fullSupportCount (r + 2) m : ℝ) := by
    exact_mod_cast fullSupportCount_pos (r + 2) m hm
  have hlog := Real.log_le_log hQ
    (show (fullSupportCount (r + 2) m : ℝ) ≤
        (numConvexDim (r + 3) m : ℝ) by
      exact_mod_cast numConvexDim_ge_fullSupport (r + 2) m)
  exact (sub_le_sub_left hlog _).trans (pair_entropy_gap_bounds r m hm).2

/-- Unconditional two-boundary entropy factorization in ambient dimension
`r+3`.  No limit shape or one-boundary asymptotic is assumed. -/
theorem convex_entropy_gap_tendsto_zero (r : ℕ) :
    Tendsto (fun m : ℕ =>
      (2 * Real.log (downsetCountDim (r + 3) m : ℝ) -
        Real.log (numConvexDim (r + 3) m : ℝ)) / (m : ℝ) ^ (r + 2))
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (pair_entropy_gap_tendsto_zero r)
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact div_nonneg (sub_nonneg.mpr (log_sandwich (r + 3) m).2) (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hQ : (0 : ℝ) < (fullSupportCount (r + 2) m : ℝ) := by
      exact_mod_cast fullSupportCount_pos (r + 2) m (by omega)
    have hlog := Real.log_le_log hQ
      (show (fullSupportCount (r + 2) m : ℝ) ≤
          (numConvexDim (r + 3) m : ℝ) by
        exact_mod_cast numConvexDim_ge_fullSupport (r + 2) m)
    exact div_le_div_of_nonneg_right (sub_le_sub_left hlog _) (by positivity)

/-- The solid-partition specialization: four-dimensional downsets and
four-dimensional convex subsets have the same leading entropy after
accounting for their one versus two boundaries. -/
theorem solid_partition_boundary_entropy_factorization :
    Tendsto (fun m : ℕ =>
      (2 * Real.log (downsetCountDim 4 m : ℝ) -
        Real.log (numConvexDim 4 m : ℝ)) / (m : ℝ) ^ 3) atTop (𝓝 0) :=
  convex_entropy_gap_tendsto_zero 1

end
end CausalAlgebraicGeometry.CAGMultidimensionalEntropy
