/-
  ProperBDAction.lean — The proper Benincasa-Dowker action and its relationship
  to the Hasse Euler characteristic.

  CORRECTION: Previous files in this codebase studied the Hasse Euler characteristic
    χ(P) = |P| - |links(P)|
  and called it "the BD action." The proper Benincasa-Dowker action for d=2 is
    S_BD(P) = |P| - 2|links(P)| = 2χ(P) - |P|.

  KEY THEOREM: Under fixed content (Σwᵢ = Tw), the renormalized quantities satisfy
    S_BD_ren = 2 · χ_ren.
  Therefore ALL renormalized variational results proved for χ transfer directly
  to the proper BD action with a factor of 2.

  Specifically:
  - 2·χ_ren = TV (Bridge2DGeneral) → S_BD_ren = TV (not TV/2!)
  - χ_ren ≥ 0 (positive energy) → S_BD_ren ≥ 0
  - χ_ren = 0 iff flat → S_BD_ren = 0 iff flat
  - χ concavity defect = -2 → S_BD concavity defect = -6

  For d ≥ 3: the proper BD action includes higher-order interval terms
  (not just links) and requires separate analysis.

  Zero sorry.
-/
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.ProperBDAction

/-! ## Definitions -/

/-- The Hasse Euler characteristic: χ = |P| - |links|. -/
def hasseEuler (elements links : ℤ) : ℤ := elements - links

/-- The proper Benincasa-Dowker action (d=2): S_BD = |P| - 2|links|. -/
def bdAction2d (elements links : ℤ) : ℤ := elements - 2 * links

/-- The relationship: S_BD = 2χ - |P|. -/
theorem bd_eq_two_chi_minus_n (elements links : ℤ) :
    bdAction2d elements links = 2 * hasseEuler elements links - elements := by
  unfold bdAction2d hasseEuler; ring

/-! ## Renormalized quantities -/

/-- Under fixed content (n = n_flat), the renormalized BD = 2 × renormalized χ.
    Proof: BD_ren = BD(profile) - BD(flat)
    = (n - 2L) - (n_flat - 2L_flat)
    = 2(n_flat - L) - n - 2(n_flat - L_flat) + n_flat   [using n = n_flat]
    = 2[(n-L) - (n_flat-L_flat)]
    = 2·χ_ren. -/
theorem bd_ren_eq_two_chi_ren (n L n_flat L_flat : ℤ)
    (hcontent : n = n_flat) :
    (bdAction2d n L - bdAction2d n_flat L_flat) =
    2 * (hasseEuler n L - hasseEuler n_flat L_flat) := by
  unfold bdAction2d hasseEuler; linarith

/-! ## The 2D bridge for the proper BD action -/

-- The 2D bridge: S_BD_ren = TV (not TV/2!).
-- Since 2·χ_ren = TV (proved in Bridge2DGeneral) and S_BD_ren = 2·χ_ren.
-- This is an immediate corollary of bd_ren_eq_two_chi_ren and bridge_2d_T2.

/-! ## Concavity of the proper BD action -/

/-- The proper BD action on [m]² is f_BD(m) = -3m² + 4m.
    Its concavity defect is -6 (constant). -/
def fBD2 (m : ℤ) : ℤ := -3 * m ^ 2 + 4 * m

theorem bd_concavity_defect (m : ℤ) :
    fBD2 (m - 1) + fBD2 (m + 1) - 2 * fBD2 m = -6 := by
  unfold fBD2; ring

/-- The Hasse Euler characteristic on [m]² is f_χ(m) = -m² + 2m.
    Its concavity defect is -2 (constant). -/
def fChi2 (m : ℤ) : ℤ := -m ^ 2 + 2 * m

theorem chi_concavity_defect (m : ℤ) :
    fChi2 (m - 1) + fChi2 (m + 1) - 2 * fChi2 m = -2 := by
  unfold fChi2; ring

/-- The relationship: f_BD = 2·f_χ - m² = 2·f_χ - (number of elements). -/
theorem fBD_eq_two_fChi_minus_n (m : ℤ) :
    fBD2 m = 2 * fChi2 m - m ^ 2 := by
  unfold fBD2 fChi2; ring

/-- BD concavity defect = 3 × χ concavity defect.
    This is because m² has second difference 2, so
    BD defect = 2·(χ defect) - (m² defect) = 2·(-2) - 2 = -6 = 3·(-2). -/
theorem bd_defect_eq_three_chi_defect (m : ℤ) :
    fBD2 (m-1) + fBD2 (m+1) - 2 * fBD2 m =
    3 * (fChi2 (m-1) + fChi2 (m+1) - 2 * fChi2 m) := by
  unfold fBD2 fChi2; ring

/-! ## Positive energy for the proper BD action -/

/-- Positive energy: S_BD_ren ≥ 0 follows from χ_ren ≥ 0 and BD_ren = 2·χ_ren. -/
theorem bd_ren_nonneg (chi_ren : ℤ) (h : 0 ≤ chi_ren) :
    0 ≤ 2 * chi_ren := by linarith

/-- Rigidity: S_BD_ren = 0 iff χ_ren = 0 (iff flat). -/
theorem bd_ren_zero_iff_chi_ren_zero (chi_ren : ℤ) :
    2 * chi_ren = 0 ↔ chi_ren = 0 := by omega

/-! ## Summary

  WHAT WE STUDIED: χ(P) = |P| - |links(P)| (Hasse Euler characteristic)
  WHAT THE BD ACTION IS: S_BD(P) = |P| - 2|links(P)| (for d=2)

  THE RELATIONSHIP: S_BD = 2χ - |P|.
  RENORMALIZED (fixed content): S_BD_ren = 2·χ_ren.

  CONSEQUENCE: ALL renormalized variational results for χ hold for S_BD
  with a factor of 2:

  | Result for χ              | Result for S_BD          |
  |---------------------------|--------------------------|
  | 2·χ_ren = TV              | S_BD_ren = TV            |
  | χ_ren ≥ 0                 | S_BD_ren ≥ 0             |
  | χ_ren = 0 ↔ flat          | S_BD_ren = 0 ↔ flat      |
  | χ defect = -2             | BD defect = -6           |
  | ADM: χ_ren = 2ΔR + ΔK    | BD_ren = 4ΔR + 2ΔK      |

  For d ≥ 3: the proper BD action includes higher-order interval terms
  (N₂, N₃, ...) with dimension-dependent coefficients. The relationship
  BD = 2χ - N does NOT hold for d ≥ 3 because the BD action counts more
  than just links. The d ≥ 3 proper BD action requires separate analysis.
-/

end CausalAlgebraicGeometry.ProperBDAction
