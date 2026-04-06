/-
  ChebyshevSeed.lean — The path graph seed of the chamber Jacobi family

  At m=d+1 (minimal chamber), K_F - I is the path graph P_{d+1},
  whose eigenvalues are 2cos(kπ/(d+2)) (Chebyshev/Dynkin A_{d+1}).

  The K_F eigenvalue ratio at m=d+1 is:
    pathRatio(d) = (1 + 2cos(π/(d+2))) / (1 + 2cos(2π/(d+2)))

  KEY THEOREM: pathRatio(d) < (d+1)/(d-1) for all d >= 2.
  This means the ratio starts BELOW the bulk target and increases
  monotonically to (d+1)/(d-1) as m -> infinity.

  Specific values:
    d=2: pathRatio = 1+sqrt(2) ~ 2.414 < 3
    d=3: pathRatio = phi = (1+sqrt(5))/2 ~ 1.618 < 2
    d=4: pathRatio = (1+sqrt(3))/2 ~ 1.366 < 5/3
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

namespace CausalAlgebraicGeometry.ChebyshevSeed

open Real

/-! ### Path graph eigenvalue ratio -/

/-- The path graph eigenvalue ratio at m=d+1:
    (1 + 2cos(pi/(d+2))) / (1 + 2cos(2pi/(d+2))). -/
noncomputable def pathRatio (d : ℕ) : ℝ :=
  (1 + 2 * cos (π / (d + 2))) / (1 + 2 * cos (2 * π / (d + 2)))

/-- The bulk target ratio (d+1)/(d-1). -/
noncomputable def bulkRatio (d : ℕ) : ℝ := ((d : ℝ) + 1) / ((d : ℝ) - 1)

/-! ### d=2: Path graph P_3, Dynkin A_3

  S eigenvalues: sqrt(2), 0, -sqrt(2)
  K_F eigenvalues: 1+sqrt(2), 1, 1-sqrt(2)
  Top R-even: 1+sqrt(2), Top R-odd: 1
  Ratio: 1+sqrt(2)
  Target: 3 -/

/-- cos(2pi/4) = cos(pi/2) = 0 -/
theorem cos_two_pi_div_four : cos (2 * π / 4) = 0 := by
  rw [show 2 * π / 4 = π / 2 from by ring]
  exact cos_pi_div_two

/-- The d=2 eigenvalue ratio denominator: 1 + 2*cos(pi/2) = 1. -/
theorem d2_denominator : 1 + 2 * cos (2 * π / ((2 : ℝ) + 2)) = 1 := by
  rw [show (2 : ℝ) + 2 = 4 from by norm_num]
  rw [cos_two_pi_div_four]
  ring

/-- The d=2 eigenvalue ratio numerator: 1 + 2*cos(pi/4) = 1 + sqrt(2). -/
theorem d2_numerator : 1 + 2 * cos (π / ((2 : ℝ) + 2)) = 1 + Real.sqrt 2 := by
  rw [show (2 : ℝ) + 2 = 4 from by norm_num]
  rw [Real.cos_pi_div_four]
  ring

/-- d=2: pathRatio = 1 + sqrt(2). -/
theorem pathRatio_d2 : pathRatio 2 = 1 + Real.sqrt 2 := by
  unfold pathRatio
  simp only [Nat.cast_ofNat]
  rw [d2_numerator, d2_denominator]
  ring

/-- sqrt(2) < 2, needed for pathRatio(2) < 3. -/
theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  nlinarith [Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]

/-- d=2: pathRatio < bulkRatio, i.e., 1 + sqrt(2) < 3. -/
theorem pathRatio_lt_bulk_d2 : pathRatio 2 < bulkRatio 2 := by
  rw [pathRatio_d2]
  unfold bulkRatio
  simp only [Nat.cast_ofNat]
  -- 1 + sqrt(2) < 3/1 = 3
  have h : Real.sqrt 2 < 2 := sqrt_two_lt_two
  norm_num
  linarith

/-! ### d=4: Path graph P_5, Dynkin A_5

  S eigenvalues: sqrt(3), 1, 0, -1, -sqrt(3)
  K_F eigenvalues: 1+sqrt(3), 2, 1, 0, 1-sqrt(3)
  Top R-even: 1+sqrt(3), Top R-odd: 2
  Ratio: (1+sqrt(3))/2
  Target: 5/3 -/

/-- cos(2pi/6) = cos(pi/3) = 1/2 -/
theorem cos_two_pi_div_six : cos (2 * π / 6) = 1 / 2 := by
  rw [show 2 * π / 6 = π / 3 from by ring]
  exact cos_pi_div_three

/-- d=4: pathRatio numerator = 1 + 2*cos(pi/6) = 1 + sqrt(3). -/
theorem d4_numerator : 1 + 2 * cos (π / ((4 : ℝ) + 2)) = 1 + Real.sqrt 3 := by
  rw [show (4 : ℝ) + 2 = 6 from by norm_num]
  rw [Real.cos_pi_div_six]
  ring

/-- d=4: pathRatio denominator = 1 + 2*cos(pi/3) = 2. -/
theorem d4_denominator : 1 + 2 * cos (2 * π / ((4 : ℝ) + 2)) = 2 := by
  rw [show (4 : ℝ) + 2 = 6 from by norm_num]
  rw [cos_two_pi_div_six]
  ring

/-- d=4: pathRatio = (1+sqrt(3))/2. -/
theorem pathRatio_d4 : pathRatio 4 = (1 + Real.sqrt 3) / 2 := by
  unfold pathRatio
  simp only [Nat.cast_ofNat]
  rw [d4_numerator, d4_denominator]

/-- sqrt(3) < 7/3, needed for pathRatio(4) < 5/3. -/
theorem sqrt_three_lt_seven_thirds : Real.sqrt 3 < 7 / 3 := by
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  -- sqrt(3) < 7/3 iff 3 < 49/9 (since sqrt(3) > 0 and 7/3 > 0)
  -- 27 < 49 iff 3*9 < 49, true
  nlinarith [Real.sqrt_nonneg 3]

/-- d=4: pathRatio < 5/3 = bulkRatio(4). -/
theorem pathRatio_lt_bulk_d4 : pathRatio 4 < bulkRatio 4 := by
  rw [pathRatio_d4]
  unfold bulkRatio
  simp only [Nat.cast_ofNat]
  -- Need: (1+sqrt(3))/2 < 5/3
  -- Equiv: 3(1+sqrt(3)) < 10, i.e., 3*sqrt(3) < 7, i.e., sqrt(3) < 7/3
  have h : Real.sqrt 3 < 7 / 3 := sqrt_three_lt_seven_thirds
  norm_num
  linarith

/-! ### d=3: Path graph P_4, Dynkin A_4

  S eigenvalues: 2cos(kpi/5) for k=1,2,3,4
    = (1+sqrt(5))/2, (sqrt(5)-1)/2, -(sqrt(5)-1)/2, -(1+sqrt(5))/2
  K_F eigenvalues: (3+sqrt(5))/2, (1+sqrt(5))/2, (3-sqrt(5))/2, (1-sqrt(5))/2
  Top R-even: (3+sqrt(5))/2, Top R-odd: (1+sqrt(5))/2
  Ratio: phi = (1+sqrt(5))/2
  Target: 2 -/

/-- cos(π/5) satisfies the minimal polynomial 4c²-2c-1=0.
    Proof: cos(3π/5) = -cos(2π/5) (supplementary angles).
    cos(3θ) = 4cos³θ-3cosθ and cos(2θ) = 2cos²θ-1.
    So 4c³-3c = -(2c²-1), giving 4c³+2c²-3c-1=0 = (c+1)(4c²-2c-1).
    Since cos(π/5)>0>-1, we get 4c²-2c-1=0. -/
theorem cos_pi_div_five_minimal_poly :
    4 * cos (π/5) ^ 2 - 2 * cos (π/5) - 1 = 0 := by
  -- Use cos(3π/5) = 4cos³(π/5)-3cos(π/5) AND cos(3π/5) = -cos(2π/5)
  -- AND cos(2π/5) = 2cos²(π/5)-1
  have h3 : cos (3*(π/5)) = 4 * cos (π/5)^3 - 3 * cos (π/5) := by
    rw [cos_three_mul]
  have h2 : cos (2*(π/5)) = 2 * cos (π/5)^2 - 1 := by
    rw [cos_two_mul]
  -- cos(3π/5) = cos(π-2π/5) = -cos(2π/5)
  have h35 : cos (3*(π/5)) = -cos (2*(π/5)) := by
    rw [show 3*(π/5) = π - 2*(π/5) from by ring]
    rw [cos_pi_sub]
  -- From h3 and h35: 4c³-3c = -(2c²-1) = 1-2c²
  -- So 4c³+2c²-3c-1 = 0, i.e., (c+1)(4c²-2c-1) = 0
  -- Since cos(π/5) ≠ -1 (it's positive), 4c²-2c-1 = 0
  -- h3: cos(3π/5) = 4c³-3c
  -- h35: cos(3π/5) = -(2c²-1) = 1-2c²
  -- So: 4c³-3c = 1-2c², i.e., 4c³+2c²-3c-1 = 0
  -- Factor: (c+1)(4c²-2c-1) = 0. Since c>0, c≠-1, so 4c²-2c-1=0.
  have hcube : 4 * cos (π/5)^3 + 2 * cos (π/5)^2 - 3 * cos (π/5) - 1 = 0 := by
    nlinarith [h3, h2, h35]
  -- Factor out (c+1): 4c³+2c²-3c-1 = (c+1)(4c²-2c-1)
  have hc_pos : 0 < cos (π/5) := by
    apply cos_pos_of_mem_Ioo; constructor
    · linarith [pi_pos]
    · linarith [pi_pos]
  have hc_ne : cos (π/5) + 1 ≠ 0 := by linarith
  -- (c+1)(4c²-2c-1) = 4c³+2c²-3c-1 = 0
  have hfac : (cos (π/5) + 1) * (4 * cos (π/5)^2 - 2 * cos (π/5) - 1) = 0 := by nlinarith
  exact (mul_eq_zero.mp hfac).resolve_left hc_ne

/-- cos(π/5) > 0 (since π/5 < π/2). -/
theorem cos_pi_div_five_pos : 0 < cos (π/5) := by
  apply cos_pos_of_mem_Ioo
  constructor
  · linarith [pi_pos]
  · have : π/5 < π/2 := by linarith [pi_pos]
    linarith

/-- cos(π/5) = (√5+1)/4.
    From 4c²-2c-1=0 and c>0: c = (2+√(4+16))/8 = (2+√20)/8 = (1+√5)/4. -/
theorem cos_pi_div_five : cos (π / 5) = (Real.sqrt 5 + 1) / 4 := by
  have hpoly := cos_pi_div_five_minimal_poly
  have hpos := cos_pi_div_five_pos
  -- cos(π/5) is the positive root of 4x²-2x-1=0
  -- The positive root is (1+√5)/4. We verify by showing the difference is zero.
  -- From 4c²-2c-1=0: c = (2±√20)/8 = (1±√5)/4
  -- Since c>0 and (1-√5)/4 < 0, we have c = (1+√5)/4.
  have h5 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  -- Strategy: show 4*(c - (1+√5)/4)*(c - (1-√5)/4) = 4c²-2c-1 = 0
  -- and c > 0 > (1-√5)/4 (since √5 > 1), so c ≠ (1-√5)/4, hence c = (1+√5)/4.
  have hother : (Real.sqrt 5 - 1) / 4 > 0 := by nlinarith [Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)]
  -- 4c²-2c-1 = 4(c-(1+√5)/4)(c-(1-√5)/4)
  have hfactor : 4 * cos (π/5) ^ 2 - 2 * cos (π/5) - 1 =
    4 * (cos (π/5) - (Real.sqrt 5 + 1)/4) * (cos (π/5) - (1 - Real.sqrt 5)/4) := by
    nlinarith [hsq]
  rw [hpoly] at hfactor
  -- So (cos(π/5) - (√5+1)/4) * (cos(π/5) - (1-√5)/4) = 0
  have := mul_eq_zero.mp (by linarith [hfactor] : (cos (π/5) - (Real.sqrt 5 + 1)/4) *
    (cos (π/5) - (1 - Real.sqrt 5)/4) = 0)
  cases this with
  | inl h => linarith
  | inr h =>
    -- cos(π/5) = (1-√5)/4 < 0, contradicting cos(π/5) > 0
    exfalso; nlinarith [hpos, hsq]

/-- cos(2π/5) = (√5-1)/4.
    From cos(2θ) = 2cos²θ-1 at θ=π/5. -/
theorem cos_two_pi_div_five : cos (2 * π / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h := cos_pi_div_five
  rw [show 2 * π / 5 = 2 * (π/5) from by ring]
  rw [cos_two_mul, h]
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  nlinarith [hsq]

/-- d=3: pathRatio numerator = (3+sqrt(5))/2. -/
theorem d3_numerator : 1 + 2 * cos (π / ((3 : ℝ) + 2)) = (3 + Real.sqrt 5) / 2 := by
  rw [show (3 : ℝ) + 2 = 5 from by norm_num]
  rw [cos_pi_div_five]
  ring

/-- d=3: pathRatio denominator = (1+sqrt(5))/2 = phi. -/
theorem d3_denominator : 1 + 2 * cos (2 * π / ((3 : ℝ) + 2)) = (1 + Real.sqrt 5) / 2 := by
  rw [show (3 : ℝ) + 2 = 5 from by norm_num]
  rw [cos_two_pi_div_five]
  ring

/-- (3+sqrt(5))/(1+sqrt(5)) = (1+sqrt(5))/2 provided sqrt(5)^2 = 5. -/
theorem golden_ratio_identity (h : Real.sqrt 5 * Real.sqrt 5 = 5) :
    (3 + Real.sqrt 5) / (1 + Real.sqrt 5) = (1 + Real.sqrt 5) / 2 := by
  have h1 : (1 + Real.sqrt 5) ≠ 0 := by
    have : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    linarith
  rw [div_eq_div_iff h1 (by norm_num : (2 : ℝ) ≠ 0)]
  nlinarith

/-- d=3: pathRatio = phi = (1+sqrt(5))/2. -/
theorem pathRatio_d3 : pathRatio 3 = (1 + Real.sqrt 5) / 2 := by
  unfold pathRatio
  simp only [Nat.cast_ofNat]
  rw [d3_numerator, d3_denominator]
  -- Goal: (3 + sqrt(5)) / 2 / ((1 + sqrt(5)) / 2) = (1 + sqrt(5)) / 2
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  exact golden_ratio_identity (Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0))

/-- sqrt(5) < 3, needed for phi < 2. -/
theorem sqrt_five_lt_three : Real.sqrt 5 < 3 := by
  have hsq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  nlinarith [Real.sqrt_nonneg 5]

/-- d=3: pathRatio < 2 = bulkRatio(3). Equiv: phi < 2, i.e., sqrt(5) < 3. -/
theorem pathRatio_lt_bulk_d3 : pathRatio 3 < bulkRatio 3 := by
  rw [pathRatio_d3]
  unfold bulkRatio
  simp only [Nat.cast_ofNat]
  -- Need: (1+sqrt(5))/2 < 4/2, i.e., sqrt(5) < 3
  have h : Real.sqrt 5 < 3 := sqrt_five_lt_three
  norm_num
  linarith

/-! ### Positivity of the denominator -/

/-- For d >= 2, cos(2pi/(d+2)) >= 0, hence 1 + 2cos(2pi/(d+2)) > 0.
    Proof: for d >= 2, 2pi/(d+2) <= pi/2, where cosine is nonneg. -/
theorem pathRatio_denom_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < 1 + 2 * cos (2 * π / ((d : ℝ) + 2)) := by
  have hd_cast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd2_pos : (0 : ℝ) < (d : ℝ) + 2 := by linarith
  -- 2pi/(d+2) <= pi/2 because d >= 2 implies d+2 >= 4
  have hle : 2 * π / ((d : ℝ) + 2) ≤ π / 2 := by
    have h4 : (4 : ℝ) ≤ (d : ℝ) + 2 := by linarith
    have hpi : 0 < π := pi_pos
    -- 2pi/(d+2) <= 2pi/4 = pi/2
    calc 2 * π / ((d : ℝ) + 2)
        ≤ 2 * π / 4 := by
          apply div_le_div_of_nonneg_left (by nlinarith [pi_pos]) (by positivity) h4
      _ = π / 2 := by ring
  have hge : 0 ≤ 2 * π / ((d : ℝ) + 2) := by positivity
  have hcos : 0 ≤ cos (2 * π / ((d : ℝ) + 2)) :=
    cos_nonneg_of_mem_Icc ⟨by linarith, hle⟩
  linarith

/-! ### Positivity of pathRatio -/

/-- For d >= 2, the numerator 1 + 2cos(pi/(d+2)) > 0.
    In fact cos(pi/(d+2)) > 0 since pi/(d+2) < pi/2. -/
theorem pathRatio_numer_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < 1 + 2 * cos (π / ((d : ℝ) + 2)) := by
  have hd_cast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd2_pos : (0 : ℝ) < (d : ℝ) + 2 := by linarith
  have hle : π / ((d : ℝ) + 2) ≤ π / 2 :=
    div_le_div_of_nonneg_left pi_pos.le (by positivity) (by linarith : (2 : ℝ) ≤ (d : ℝ) + 2)
  have hcos : 0 ≤ cos (π / ((d : ℝ) + 2)) :=
    cos_nonneg_of_mem_Icc ⟨by nlinarith [pi_pos, div_nonneg pi_pos.le hd2_pos.le], hle⟩
  linarith

/-- For d >= 2, pathRatio(d) > 0. -/
theorem pathRatio_pos (d : ℕ) (hd : 2 ≤ d) : 0 < pathRatio d := by
  unfold pathRatio
  exact div_pos (pathRatio_numer_pos d hd) (pathRatio_denom_pos d hd)

/-! ### The general inequality -/

/-- For d ≥ 5: cos(π/(d+2)) > d/(d+1). Uses π² < 16 and 2(d+2)²>16(d+1) for d≥5. -/
private theorem cos_gt_ratio_ge5 (d : ℕ) (hd : 5 ≤ d) :
    (d:ℝ)/((d:ℝ)+1) < cos (π / ((d:ℝ)+2)) := by
  have hd' : (5:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h1 : (0:ℝ) < (d:ℝ)+1 := by linarith
  have h2 : (0:ℝ) < (d:ℝ)+2 := by linarith
  have hcos := @one_sub_sq_div_two_le_cos (π/((d:ℝ)+2))
  suffices h : (d:ℝ)/((d:ℝ)+1) < 1 - (π/((d:ℝ)+2))^2/2 by linarith
  -- π² < 16 from π < 4
  have hpi_sq : π ^ 2 < 16 := by nlinarith [pi_lt_four, pi_nonneg]
  -- 2(d+2)² > 16(d+1) for d ≥ 5: 2d²-8d-8 ≥ 2·25-40-8 = 2 > 0
  have hkey : 16 * ((d:ℝ)+1) < 2 * ((d:ℝ)+2) ^ 2 := by nlinarith
  have hkey2 : π ^ 2 * ((d:ℝ)+1) < 2 * ((d:ℝ)+2) ^ 2 := by nlinarith
  -- d/(d+1) = 1 - 1/(d+1) < 1 - π²/(2(d+2)²) iff 1/(d+1) > π²/(2(d+2)²)
  -- iff 2(d+2)² > π²(d+1) ← hkey2
  rw [div_lt_iff₀ h1]
  have h_ne2 : ((d:ℝ)+2) ≠ 0 := ne_of_gt h2
  -- LHS = d. RHS = (d+1) - (π/(d+2))²/2 · (d+1)
  -- = (d+1) - π²(d+1)/(2(d+2)²)
  -- d < (d+1) - π²(d+1)/(2(d+2)²) iff π²(d+1)/(2(d+2)²) < 1
  have : (π / ((d:ℝ)+2)) ^ 2 / 2 * ((d:ℝ)+1) =
    π^2*((d:ℝ)+1) / (2*((d:ℝ)+2)^2) := by field_simp
  nlinarith [div_lt_one (show 0 < 2*((d:ℝ)+2)^2 by positivity) |>.mpr hkey2]

theorem cos_gt_ratio (d : ℕ) (hd : 2 ≤ d) :
    (d:ℝ)/((d:ℝ)+1) < cos (π / ((d:ℝ)+2)) := by
  by_cases h5 : 5 ≤ d
  · exact cos_gt_ratio_ge5 d h5
  · -- d ∈ {2,3,4}
    have hd_lt : d < 5 := by omega
    interval_cases d
    · -- d=2: 2/3 < cos(π/4) = √2/2
      simp only [Nat.cast_ofNat]; rw [show (2:ℝ)+2=4 from by norm_num, Real.cos_pi_div_four]
      have := Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    · -- d=3: 3/4 < cos(π/5) = (1+√5)/4
      simp only [Nat.cast_ofNat]; rw [show (3:ℝ)+2=5 from by norm_num, cos_pi_div_five]
      have := Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 5]
    · -- d=4: 4/5 < cos(π/6) = √3/2
      simp only [Nat.cast_ofNat]; rw [show (4:ℝ)+2=6 from by norm_num, Real.cos_pi_div_six]
      have := Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 3]

theorem pathRatio_lt_bulkRatio (d : ℕ) (hd : 2 ≤ d) :
    pathRatio d < bulkRatio d := by
  unfold pathRatio bulkRatio
  have hd' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hd1 : (0:ℝ) < (d:ℝ) - 1 := by linarith
  have hdenom_pos := pathRatio_denom_pos d hd
  rw [div_lt_div_iff₀ hdenom_pos hd1]
  have hcos2 : cos (2*π/((d:ℝ)+2)) = 2*(cos (π / ((d:ℝ)+2)))^2 - 1 := by
    rw [show 2*π/((d:ℝ)+2) = 2*(π/((d:ℝ)+2)) from by ring]
    exact cos_two_mul _
  rw [hcos2]
  have hc_gt := cos_gt_ratio d hd
  -- c > d/(d+1) > 0, so c+1/2 > 0 and c-d/(d+1) > 0.
  -- Need: (d-1)(1+2c) < (d+1)(4c²-1)
  -- i.e., d-1+2(d-1)c < 4(d+1)c²-(d+1), i.e., 4(d+1)c²-2(d-1)c-2d > 0
  -- Use: c > d/(d+1) means c*(d+1) > d, so c*(d+1)-d > 0.
  -- Also c > 0 (from c > d/(d+1) > 0).
  have hc_pos : 0 < cos (π / ((d:ℝ)+2)) := by
    linarith [div_pos (by linarith : (0:ℝ) < d) (by linarith : (0:ℝ) < (d:ℝ)+1)]
  -- Direct nlinarith with explicit products
  have h_cd : (d:ℝ) < cos (π/((d:ℝ)+2)) * ((d:ℝ)+1) := by
    have := (div_lt_iff₀ (show (0:ℝ) < (d:ℝ)+1 by linarith)).mp hc_gt
    linarith
  nlinarith [sq_nonneg (cos (π/((d:ℝ)+2))), mul_pos hc_pos (show 0 < (d:ℝ)+1 by linarith)]

/-! ### Connection to Dynkin diagrams -/

/-- The k-th eigenvalue of K_F at m=d+1 is 1 + 2cos(k*pi/(d+2)).
    The path graph P_{d+1} is the Dynkin diagram A_{d+1} of SU(d+2).
    The eigenvalues 2cos(k*pi/(d+2)) are the Chebyshev values.
    At minimal m=d+1, the chamber kernel K_F = I + adj(P_{d+1}). -/
noncomputable def chebyshevEigenvalue (d k : ℕ) : ℝ :=
  1 + 2 * cos ((k : ℝ) * π / ((d : ℝ) + 2))

/-- The top eigenvalue (k=1) matches pathRatio numerator. -/
theorem top_eigenvalue (d : ℕ) :
    chebyshevEigenvalue d 1 = 1 + 2 * cos (π / ((d : ℝ) + 2)) := by
  unfold chebyshevEigenvalue
  simp

/-- Eigenvalue pairing: lambda_k + lambda_{d+2-k} = 2.
    This is cos(x) + cos(pi-x) = 0 shifted by I. -/
theorem eigenvalue_pairing (d k : ℕ) (_hk : 1 ≤ k) (hk2 : k ≤ d + 1) :
    chebyshevEigenvalue d k + chebyshevEigenvalue d (d + 2 - k) = 2 := by
  unfold chebyshevEigenvalue
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hdk : (k : ℝ) ≤ (d : ℝ) + 1 := by exact_mod_cast hk2
  -- (d+2-k)*pi/(d+2) = pi - k*pi/(d+2)
  have hkey : ((d + 2 - k : ℕ) : ℝ) * π / ((d : ℝ) + 2) = π - (k : ℝ) * π / ((d : ℝ) + 2) := by
    have hsub : ((d + 2 - k : ℕ) : ℝ) = (d : ℝ) + 2 - (k : ℝ) := by
      have : k ≤ d + 2 := by omega
      rw [Nat.cast_sub this]
      push_cast; ring
    rw [hsub]
    field_simp
  rw [hkey, cos_pi_sub]
  ring

/-! ### Deformation summary

  PROVED (0 sorry):
  - pathRatio_d2 = 1 + sqrt(2)
  - pathRatio_lt_bulk_d2: 1 + sqrt(2) < 3
  - pathRatio_d4 = (1+sqrt(3))/2
  - pathRatio_lt_bulk_d4: (1+sqrt(3))/2 < 5/3
  - pathRatio_denom_pos, pathRatio_numer_pos, pathRatio_pos
  - sqrt_two_lt_two, sqrt_three_lt_seven_thirds, sqrt_five_lt_three

  PROVED (modulo cos(pi/5), cos(2pi/5) pentagon identities):
  - pathRatio_d3 = phi = (1+sqrt(5))/2
  - pathRatio_lt_bulk_d3: phi < 2
  - golden_ratio_identity

  SORRY (3 total):
  - cos_pi_div_five, cos_two_pi_div_five (pentagon identities, not in Mathlib)
  - pathRatio_lt_bulkRatio (general d, needs Taylor bounds on cos)

  KEY INSIGHT: The chamber Jacobi family J_d is a continuous deformation
  of the Chebyshev/path-graph seed. At m=d+1 (minimal chamber), the
  eigenvalue ratio equals pathRatio(d) < (d+1)/(d-1) = bulkRatio(d),
  and it increases monotonically to the bulk value as m -> infinity.
  The path graph is the Dynkin diagram A_{d+1} of SU(d+2), connecting
  chamber fermions to Lie theory at the minimal chamber.
-/

end CausalAlgebraicGeometry.ChebyshevSeed
