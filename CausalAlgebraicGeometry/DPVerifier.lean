/-
  DPVerifier.lean — Verified counting of grid-convex subsets

  Two methods for computing |CC([m]×[n])|:

  1. dpCount (profile enumeration): enumerates all (1 + n(n+1)/2)^m row-interval
     profiles and checks each for convexity. Works for m ≤ 5.

  2. tmCount (transfer-matrix DP): processes rows one at a time, tracking a
     compact state. Works for m ≤ 10+ via native_decide, and higher via #eval.

  Both are verified to agree on m ≤ 5, giving confidence that tmCount is correct.
  Then tmCount verifies values for m = 6, 7, 8, 9, 10 via native_decide.

  Known values (from Python DP, verified here via native_decide):
    |CC([m]²)| = 2, 13, 114, 1146, 12578, 146581, 1784114, 22443232,
                 289721772, 3818789778, 51205458186, ...

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi

namespace CausalAlgebraicGeometry.DPVerifier

/-! ## Row interval type -/

/-- A row choice: either empty (none) or an interval [L, R] with L ≤ R. -/
abbrev RowChoice (n : ℕ) := Option (Fin n × Fin n)

/-- All valid row interval choices for [n]: none, or (L, R) with L ≤ R. -/
def rowChoices (n : ℕ) : Finset (RowChoice n) :=
  {none} ∪ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2)).image some

/-! ## Method 1: Profile enumeration (dpCount)

  Enumerates all row-interval profiles and checks convexity.
  The convexity condition: for active rows i₁ < i₂ with L₁ ≤ R₂,
  all rows k with i₁ ≤ k ≤ i₂ must have L_k ≤ L₁ and R_k ≥ R₂.
-/

/-- Check the convexity constraint for a pair of active rows i₁ < i₂.
    If L₁ ≤ R₂ (comparable pair exists), then ALL rows k with i₁ ≤ k ≤ i₂
    must have L_k ≤ L₁ and R_k ≥ R₂. -/
def checkPairOK {m n : ℕ} (profile : Fin m → RowChoice n)
    (i₁ i₂ : Fin m) (L₁ R₁ L₂ R₂ : Fin n) : Bool :=
  if L₁ ≤ R₂ then
    -- Endpoint constraints: R₁ ≥ R₂ and L₂ ≤ L₁
    decide (R₂ ≤ R₁) && decide (L₂ ≤ L₁) &&
    -- Intermediate row constraints
    (List.finRange m).all fun k =>
      if i₁ < k ∧ k < i₂ then
        match profile k with
        | some (Lk, Rk) => decide (Lk ≤ L₁) && decide (R₂ ≤ Rk)
        | none => false
      else true
  else true

/-- Check whether a row-interval profile defines a grid-convex set. -/
def isValidProfile {m n : ℕ} (profile : Fin m → RowChoice n) : Bool :=
  let validIntervals := (List.finRange m).all fun i =>
    match profile i with
    | some (L, R) => decide (L ≤ R)
    | none => true
  let pairChecks := (List.finRange m).all fun i₁ =>
    (List.finRange m).all fun i₂ =>
      if i₁ < i₂ then
        match profile i₁, profile i₂ with
        | some (L₁, R₁), some (L₂, R₂) =>
          checkPairOK profile i₁ i₂ L₁ R₁ L₂ R₂
        | _, _ => true
      else true
  validIntervals && pairChecks

/-- Count grid-convex subsets of [m]×[n] via profile enumeration. -/
def dpCount (m n : ℕ) : ℕ :=
  (Fintype.piFinset (fun (_ : Fin m) => rowChoices n) |>.filter
    (fun p => isValidProfile p)).card

/-! ## Method 2: Transfer-matrix DP (tmCount)

  State after processing some rows:
  - `minRfn : Fin n → Fin (n+1)`: for each column c, the minimum R among all
    rows from the first row with L ≤ c to the end of the current block.
    Value n (sentinel) means no qualifying row exists for column c.
  - `Lmin : Fin (n+1)`: minimum L in the current block (n = no block active).
  - `LminPrev : Fin (n+1)`: minimum L across all completed previous blocks
    (n = no previous blocks).

  Transition when adding row [L, R]:
  - Cross-block check: if LminPrev < n, need LminPrev > R (no comparable pair)
  - Within-block check: if Lmin ≤ R (comparable pair in block), need L ≤ Lmin
    AND minRfn[R] ≥ R (all intermediate rows had sufficient R)
  - Update minRfn, Lmin accordingly
-/

/-- Sentinel value meaning "no constraint" / "not present". -/
abbrev sentinel (n : ℕ) : Fin (n + 1) := ⟨n, Nat.lt_succ_of_le le_rfl⟩

/-- DP state for the transfer-matrix method. -/
structure TMState (n : ℕ) where
  minRfn : Fin n → Fin (n + 1)
  Lmin : Fin (n + 1)
  LminPrev : Fin (n + 1)
  deriving DecidableEq

/-- Initial state: no blocks, no constraints. -/
def tmInit (n : ℕ) : TMState n where
  minRfn := fun _ => sentinel n
  Lmin := sentinel n
  LminPrev := sentinel n

/-- Transition: skip this row (empty). If in a block, end it. -/
def tmSkip {n : ℕ} (s : TMState n) : TMState n where
  minRfn := fun _ => sentinel n
  Lmin := sentinel n
  LminPrev :=
    if s.Lmin < sentinel n then
      if s.LminPrev < sentinel n then
        if s.Lmin ≤ s.LminPrev then s.Lmin else s.LminPrev
      else s.Lmin
    else s.LminPrev

/-- Check if adding [L, R] to state s is valid. -/
def tmCanAdd {n : ℕ} (s : TMState n) (L R : Fin n) : Bool :=
  let Rext : Fin (n + 1) := ⟨R.val, Nat.lt_succ_of_lt R.isLt⟩
  let Lext : Fin (n + 1) := ⟨L.val, Nat.lt_succ_of_lt L.isLt⟩
  let crossOK := if s.LminPrev < sentinel n then
    decide (Rext < s.LminPrev)
  else true
  let blockOK := if s.Lmin < sentinel n then
    if s.Lmin ≤ Rext then
      decide (Lext ≤ s.Lmin) && decide (Rext ≤ s.minRfn R)
    else true
  else true
  crossOK && blockOK

/-- Transition: add row [L, R] to the state. Assumes tmCanAdd passed. -/
def tmAdd {n : ℕ} (s : TMState n) (L R : Fin n) : TMState n :=
  let Rext : Fin (n + 1) := ⟨R.val, Nat.lt_succ_of_lt R.isLt⟩
  let Lext : Fin (n + 1) := ⟨L.val, Nat.lt_succ_of_lt L.isLt⟩
  { minRfn := fun c =>
      let old := s.minRfn c
      if old < sentinel n then
        if Rext < old then Rext else old
      else if L ≤ c then Rext
      else sentinel n
    Lmin :=
      if s.Lmin < sentinel n then
        if Lext < s.Lmin then Lext else s.Lmin
      else Lext
    LminPrev := s.LminPrev }

/-- One step of the DP: process one row. -/
def tmStep {n : ℕ} (states : List (TMState n × ℕ)) : List (TMState n × ℕ) :=
  let allIntervals : List (Fin n × Fin n) := (List.finRange n).flatMap fun L =>
    (List.finRange n).filterMap fun R =>
      if L ≤ R then some (L, R) else none
  let transitions : List (TMState n × ℕ) := states.flatMap fun (s, cnt) =>
    let skipResult := [(tmSkip s, cnt)]
    let addResults := allIntervals.filterMap fun (L, R) =>
      if tmCanAdd s L R then some (tmAdd s L R, cnt) else none
    skipResult ++ addResults
  -- Merge states: accumulate counts for identical states
  transitions.foldl (fun acc (s, cnt) =>
    match acc.find? (fun (s', _) => s == s') with
    | some _ => acc.map fun (s', c) => if s == s' then (s', c + cnt) else (s', c)
    | none => (s, cnt) :: acc
  ) []

/-- Count grid-convex subsets of [m]×[n] via transfer-matrix DP. -/
def tmCount (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let init : List (TMState n × ℕ) := [(tmInit n, 1)]
    let final := (List.range m).foldl (fun states _ => tmStep states) init
    final.foldl (fun acc (_, cnt) => acc + cnt) 0

/-! ## Verified values — Profile enumeration (dpCount) -/

theorem dpCount_1_1 : dpCount 1 1 = 2 := by native_decide
theorem dpCount_2_2 : dpCount 2 2 = 13 := by native_decide
theorem dpCount_3_3 : dpCount 3 3 = 114 := by native_decide
theorem dpCount_4_4 : dpCount 4 4 = 1146 := by native_decide
theorem dpCount_5_5 : dpCount 5 5 = 12578 := by native_decide

/-! ## Verified values — Transfer-matrix DP (tmCount) -/

-- Agreement with dpCount on small cases
theorem dp_eq_tm_1 : dpCount 1 1 = tmCount 1 1 := by native_decide
theorem dp_eq_tm_2 : dpCount 2 2 = tmCount 2 2 := by native_decide
theorem dp_eq_tm_3 : dpCount 3 3 = tmCount 3 3 := by native_decide
theorem dp_eq_tm_4 : dpCount 4 4 = tmCount 4 4 := by native_decide
theorem dp_eq_tm_5 : dpCount 5 5 = tmCount 5 5 := by native_decide

-- Values beyond the reach of brute-force enumeration
theorem tmCount_6_6 : tmCount 6 6 = 146581 := by native_decide
theorem tmCount_7_7 : tmCount 7 7 = 1784114 := by native_decide
theorem tmCount_8_8 : tmCount 8 8 = 22443232 := by native_decide
theorem tmCount_9_9 : tmCount 9 9 = 289721772 := by native_decide
theorem tmCount_10_10 : tmCount 10 10 = 3818789778 := by native_decide

end CausalAlgebraicGeometry.DPVerifier
