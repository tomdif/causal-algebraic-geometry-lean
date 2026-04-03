/-
  AnomalyVerification.lean — Explicit verification of all 6 anomaly conditions

  Given the SM spectrum (one generation, all as left-handed Weyl):
    Q_L   = (3, 2, Y = 1/6)
    u_R^c = (3̄, 1, Y = -2/3)
    d_R^c = (3̄, 1, Y = 1/3)
    L_L   = (1, 2, Y = -1/2)
    e_R^c = (1, 1, Y = 1)

  We verify that all 6 anomaly conditions cancel:
    [SU(3)]²U(1), [SU(2)]²U(1), [U(1)]³, grav²U(1),
    SU(2) Witten (global), [SU(3)]³

  These are ARITHMETIC FACTS about the charge assignments.
  The charges themselves are derived in AnomalyConstraints.lean
  (unified theory repo) from anomaly cancellation as a constraint.

  This file provides the CONSISTENCY CHECK: the derived charges
  do satisfy all anomaly conditions, including the ones not used
  in the original derivation (cubic U(1), Witten).
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace CausalAlgebraicGeometry.AnomalyVerification

/-! ### SM Spectrum: one generation, all left-handed Weyl -/

/-- Hypercharges of SM fermions (one generation, left-handed Weyl convention). -/
def Y_QL : ℚ := 1/6      -- quark doublet
def Y_uRc : ℚ := -2/3    -- anti-right-up
def Y_dRc : ℚ := 1/3     -- anti-right-down
def Y_LL : ℚ := -1/2     -- lepton doublet
def Y_eRc : ℚ := 1       -- anti-right-electron

/-- Color multiplicities. -/
def Nc_QL : ℚ := 3
def Nc_uRc : ℚ := 3
def Nc_dRc : ℚ := 3
def Nc_LL : ℚ := 1
def Nc_eRc : ℚ := 1

/-- Weak multiplicities. -/
def Nw_QL : ℚ := 2
def Nw_uRc : ℚ := 1
def Nw_dRc : ℚ := 1
def Nw_LL : ℚ := 2
def Nw_eRc : ℚ := 1

/-! ### Anomaly 1: [SU(3)]² × U(1)
    Σ T(R_c) × N_w × Y over SU(3) non-singlets.
    T(fund) = 1/2. -/
def anomaly_SU3sq_U1 : ℚ :=
  1/2 * Nw_QL * Y_QL + 1/2 * Nw_uRc * Y_uRc + 1/2 * Nw_dRc * Y_dRc

theorem anomaly_SU3sq_U1_vanishes : anomaly_SU3sq_U1 = 0 := by native_decide

/-! ### Anomaly 2: [SU(2)]² × U(1)
    Σ T(R_w) × N_c × Y over SU(2) non-singlets.
    T(fund) = 1/2. -/
def anomaly_SU2sq_U1 : ℚ :=
  1/2 * Nc_QL * Y_QL + 1/2 * Nc_LL * Y_LL

theorem anomaly_SU2sq_U1_vanishes : anomaly_SU2sq_U1 = 0 := by native_decide

/-! ### Anomaly 3: [U(1)]³
    Σ N_c × N_w × Y³. -/
def anomaly_U1_cubed : ℚ :=
  Nc_QL * Nw_QL * Y_QL^3 + Nc_uRc * Nw_uRc * Y_uRc^3 +
  Nc_dRc * Nw_dRc * Y_dRc^3 + Nc_LL * Nw_LL * Y_LL^3 +
  Nc_eRc * Nw_eRc * Y_eRc^3

theorem anomaly_U1_cubed_vanishes : anomaly_U1_cubed = 0 := by native_decide

/-! ### Anomaly 4: grav² × U(1)
    Σ N_c × N_w × Y. -/
def anomaly_grav_U1 : ℚ :=
  Nc_QL * Nw_QL * Y_QL + Nc_uRc * Nw_uRc * Y_uRc +
  Nc_dRc * Nw_dRc * Y_dRc + Nc_LL * Nw_LL * Y_LL +
  Nc_eRc * Nw_eRc * Y_eRc

theorem anomaly_grav_U1_vanishes : anomaly_grav_U1 = 0 := by native_decide

/-! ### Anomaly 5: SU(2) Witten global anomaly
    Number of SU(2) doublets (with color multiplicity) must be even. -/
def su2_doublet_count : ℕ := 3 * 1 + 1 * 1  -- Q_L (3 colors) + L_L (1 color)

theorem su2_witten_even : su2_doublet_count % 2 = 0 := by native_decide

/-! ### Anomaly 6: [SU(3)]³
    A(3) - A(3̄) = 0 (equal fundamentals and anti-fundamentals). -/
def su3_cubic : ℤ := 2 - 1 - 1  -- Q_L (doublet=2) - u_R^c - d_R^c

theorem su3_cubic_vanishes : su3_cubic = 0 := by native_decide

/-! ### Master theorem: all 6 anomaly conditions -/

theorem all_anomalies_cancel :
    anomaly_SU3sq_U1 = 0 ∧
    anomaly_SU2sq_U1 = 0 ∧
    anomaly_U1_cubed = 0 ∧
    anomaly_grav_U1 = 0 ∧
    su2_doublet_count % 2 = 0 ∧
    su3_cubic = 0 :=
  ⟨anomaly_SU3sq_U1_vanishes, anomaly_SU2sq_U1_vanishes,
   anomaly_U1_cubed_vanishes, anomaly_grav_U1_vanishes,
   su2_witten_even, su3_cubic_vanishes⟩

/-! ### Interpretation

These are ARITHMETIC FACTS about the SM charge assignments
(Y_Q = 1/6, Y_u = -2/3, Y_d = 1/3, Y_L = -1/2, Y_e = 1)
with N_c = 3, N_w = 2.

The charges are derived in AnomalyConstraints.lean (unified theory repo)
from anomaly cancellation as a CONSTRAINT. This file verifies that
the derived charges indeed satisfy ALL SIX conditions, including:
  - The cubic [U(1)]³ (not used in the original derivation)
  - The SU(2) Witten global anomaly (not used in the original derivation)

This is a strong CONSISTENCY CHECK: the anomaly system is overdetermined
(6 conditions on 4 charge ratios), and all 6 are satisfied simultaneously.

What this does NOT do: derive anomaly cancellation from the chamber theory.
The chamber theory provides a lattice regularization where the full
vectorlike determinant is gauge-invariant. The CHIRAL anomaly conditions
are verified here as arithmetic consequences of the charge assignments,
not derived from the lattice structure itself.
-/

end CausalAlgebraicGeometry.AnomalyVerification
