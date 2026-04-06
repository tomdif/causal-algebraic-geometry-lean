/-
  GapTheorem.lean — The GAP POSITIVITY theorem

  For all d >= 3, the eigenvalue lambda* = (d-1)/(d+1) satisfies:
    0 < lambda* < 1
  and the spectral gap gamma_d = ln((d+1)/(d-1)) is positive.

  Specific values:
    d=3: lambda* = 1/2, gamma = ln(2)
    d=4: lambda* = 3/5, gamma = ln(5/3)
    d=5: lambda* = 2/3, gamma = ln(2)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace CausalAlgebraicGeometry.GapTheorem

open Real

/-! ## The eigenvalue (d-1)/(d+1) -/

/-- The eigenvalue is positive for d >= 3. -/
theorem eigenvalue_pos (d : ℕ) (hd : 3 ≤ d) :
    0 < ((d:ℝ) - 1) / ((d:ℝ) + 1) := by
  have hd' : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  apply div_pos <;> linarith

/-- The eigenvalue is less than 1 for d >= 3. -/
theorem eigenvalue_lt_one (d : ℕ) (hd : 3 ≤ d) :
    ((d:ℝ) - 1) / ((d:ℝ) + 1) < 1 := by
  have hd' : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  rw [div_lt_one (by linarith : 0 < (d:ℝ) + 1)]
  linarith

/-- The eigenvalue is in (0,1) for d >= 3. -/
theorem eigenvalue_in_unit (d : ℕ) (hd : 3 ≤ d) :
    0 < ((d:ℝ) - 1) / ((d:ℝ) + 1) ∧ ((d:ℝ) - 1) / ((d:ℝ) + 1) < 1 :=
  ⟨eigenvalue_pos d hd, eigenvalue_lt_one d hd⟩

/-! ## The spectral gap ln((d+1)/(d-1)) -/

/-- The spectral gap is positive for d >= 3. -/
theorem gap_pos (d : ℕ) (hd : 3 ≤ d) :
    0 < log (((d:ℝ) + 1) / ((d:ℝ) - 1)) := by
  have hd' : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  apply log_pos
  rw [one_lt_div (by linarith : 0 < (d:ℝ) - 1)]
  linarith

/-- The gap ratio (d+1)/(d-1) is greater than 1 for d >= 3. -/
theorem gap_ratio_gt_one (d : ℕ) (hd : 3 ≤ d) :
    1 < ((d:ℝ) + 1) / ((d:ℝ) - 1) := by
  have hd' : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  rw [one_lt_div (by linarith : 0 < (d:ℝ) - 1)]
  linarith

/-- The gap ratio equals the reciprocal of the eigenvalue. -/
theorem gap_ratio_eq_reciprocal (d : ℕ) (hd : 3 ≤ d) :
    ((d:ℝ) + 1) / ((d:ℝ) - 1) = 1 / (((d:ℝ) - 1) / ((d:ℝ) + 1)) := by
  have hd' : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h1 : ((d:ℝ) - 1) ≠ 0 := by linarith
  rw [one_div, inv_div]

/-- The eigenvalue approaches 1 as d -> infinity: lambda* = 1 - 2/(d+1). -/
theorem eigenvalue_asymptotic (d : ℕ) (hd : 3 ≤ d) :
    ((d:ℝ) - 1) / ((d:ℝ) + 1) = 1 - 2 / ((d:ℝ) + 1) := by
  have hd' : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have : ((d:ℝ) + 1) ≠ 0 := by linarith
  field_simp; ring

/-! ## Specific dimension values -/

/-- d=3: eigenvalue = 1/2. -/
theorem eigenvalue_d3 : ((3:ℝ) - 1) / ((3:ℝ) + 1) = 1/2 := by norm_num

/-- d=4: eigenvalue = 3/5. -/
theorem eigenvalue_d4 : ((4:ℝ) - 1) / ((4:ℝ) + 1) = 3/5 := by norm_num

/-- d=5: eigenvalue = 2/3. -/
theorem eigenvalue_d5 : ((5:ℝ) - 1) / ((5:ℝ) + 1) = 2/3 := by norm_num

/-- d=6: eigenvalue = 5/7. -/
theorem eigenvalue_d6 : ((6:ℝ) - 1) / ((6:ℝ) + 1) = 5/7 := by norm_num

/-- d=3: gap ratio = 2. -/
theorem gap_ratio_d3 : ((3:ℝ) + 1) / ((3:ℝ) - 1) = 2 := by norm_num

/-- d=4: gap ratio = 5/3. -/
theorem gap_ratio_d4 : ((4:ℝ) + 1) / ((4:ℝ) - 1) = 5/3 := by norm_num

/-- d=5: gap ratio = 3/2. -/
theorem gap_ratio_d5 : ((5:ℝ) + 1) / ((5:ℝ) - 1) = 3/2 := by norm_num

/-- d=3: gap = ln(2). -/
theorem gap_d3_pos : 0 < log (((3:ℝ) + 1) / ((3:ℝ) - 1)) := by
  apply log_pos; norm_num

/-- d=4: gap = ln(5/3). -/
theorem gap_d4_pos : 0 < log (((4:ℝ) + 1) / ((4:ℝ) - 1)) := by
  apply log_pos; norm_num

/-- d=5: gap = ln(3/2). -/
theorem gap_d5_pos : 0 < log (((5:ℝ) + 1) / ((5:ℝ) - 1)) := by
  apply log_pos; norm_num

/-! ## The gap is monotone decreasing in d

For d1 < d2: (d2-1)/(d2+1) > (d1-1)/(d1+1), so the eigenvalue increases,
and the gap ratio (d+1)/(d-1) decreases, hence the gap decreases. -/

/-- The eigenvalue is increasing in d: if d1 < d2 then lambda*(d1) < lambda*(d2). -/
theorem eigenvalue_increasing (d1 d2 : ℕ) (hd1 : 3 ≤ d1) (h : d1 < d2) :
    ((d1:ℝ) - 1) / ((d1:ℝ) + 1) < ((d2:ℝ) - 1) / ((d2:ℝ) + 1) := by
  have hd1' : (3:ℝ) ≤ (d1:ℝ) := by exact_mod_cast hd1
  have hlt : (d1:ℝ) < (d2:ℝ) := by exact_mod_cast h
  have h1 : 0 < (d1:ℝ) + 1 := by linarith
  have h2 : 0 < (d2:ℝ) + 1 := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

end CausalAlgebraicGeometry.GapTheorem
