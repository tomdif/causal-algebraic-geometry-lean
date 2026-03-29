/-
Copyright (c) 2026 Thomas DiFiore. All rights reserved.
LGV Lattice Path Definitions for the 2-path case.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.LGV

/-! ## Lattice paths as subsets

A lattice path from (0, a) to (n, b) with a ≥ b uses n East steps and (a-b) South steps.
Total steps: n + (a - b). We encode the path as the SET of positions (among 0..total-1)
where East steps occur. This is an n-element subset of Fin(n + (a-b)).

The number of such paths is C(n + (a-b), n).

For our application:
- Path type 1 (σ=id, path₁): (0,m+1) → (m,1), total = 2m, East count = m → C(2m, m)
- Path type 2 (σ=id, path₂): (0,m) → (m,0), total = 2m, East count = m → C(2m, m)
- Path type 3 (σ=swap, path₁): (0,m+1) → (m,0), total = 2m+1, East count = m → C(2m+1, m)
- Path type 4 (σ=swap, path₂): (0,m) → (m,1), total = 2m-1, East count = m → C(2m-1, m)
-/

/-- A lattice path encoded as a subset of step positions where East steps occur.
    `total` = total number of steps, `eastCount` = number of East steps. -/
structure LPath (total eastCount : ℕ) where
  eastPositions : Finset (Fin total)
  card_eq : eastPositions.card = eastCount

/-- The number of East steps among the first `k` steps. -/
def LPath.eastsBeforeStep {total eastCount : ℕ} (p : LPath total eastCount)
    (k : ℕ) : ℕ :=
  (p.eastPositions.filter (fun i => i.val < k)).card

/-- The height of the path after step k, starting at height `startHeight`.
    Height decreases by 1 for each South step and stays the same for each East step.
    Equivalently: height = startHeight - (number of South steps in first k steps)
                        = startHeight - (k - number of East steps in first k steps) -/
def LPath.heightAfterStep {total eastCount : ℕ} (p : LPath total eastCount)
    (startHeight : ℤ) (k : ℕ) : ℤ :=
  startHeight - ((k : ℤ) - (p.eastsBeforeStep k : ℤ))

/-- The x-coordinate (column) after step k = number of East steps so far. -/
def LPath.xAfterStep {total eastCount : ℕ} (p : LPath total eastCount)
    (k : ℕ) : ℕ :=
  p.eastsBeforeStep k

/-- The grid point visited after step k. -/
def LPath.pointAfterStep {total eastCount : ℕ} (p : LPath total eastCount)
    (startHeight : ℤ) (k : ℕ) : ℤ × ℤ :=
  ((p.xAfterStep k : ℤ), p.heightAfterStep startHeight k)

/-- The set of ALL grid points visited by the path (at each step boundary). -/
noncomputable def LPath.gridPoints {total eastCount : ℕ} (p : LPath total eastCount)
    (startHeight : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.range (total + 1)).image (fun k => p.pointAfterStep startHeight k)

/-- Two paths share a grid point. -/
def pathsSharePoint {t₁ e₁ t₂ e₂ : ℕ}
    (p₁ : LPath t₁ e₁) (h₁ : ℤ) (p₂ : LPath t₂ e₂) (h₂ : ℤ) : Prop :=
  (p₁.gridPoints h₁ ∩ p₂.gridPoints h₂).Nonempty

/-- The set of all n-element subsets of Fin total, representing all lattice paths. -/
noncomputable def pathSubsets (total eastCount : ℕ) : Finset (Finset (Fin total)) :=
  (Finset.univ : Finset (Finset (Fin total))).filter (fun s => s.card = eastCount)

/-- The number of lattice paths from (0, a) to (n, b) with a ≥ b equals C(n+(a-b), n). -/
theorem count_paths (n a b : ℕ) (hab : b ≤ a) :
    (pathSubsets (n + (a - b)) n).card = Nat.choose (n + (a - b)) n := by
  -- Each path is determined by choosing which n positions (out of n+(a-b)) are East steps.
  -- This is C(n + (a-b), n) by definition of binomial coefficients.
  sorry -- TODO: use Finset.card_powersetCard

end CausalAlgebraicGeometry.LGV
