/-
  SectorDecomposition.lean — Block decomposition of convex subsets of [m]²

  A convex subset of [m]² decomposes into "blocks" — maximal contiguous runs
  of nonempty rows. The sector decomposition counts how many convex subsets
  have exactly k blocks.

  Main definitions:
  - `numBlocks`: number of maximal contiguous runs of nonempty rows in a profile
  - `sectorCount m n k`: number of convex subsets of [m]×[n] with exactly k blocks
  - `solidCount m n`: number of convex subsets of [m]×[n] with ALL rows nonempty

  Main results (zero sorry, zero custom axioms):
  - Computational: sectorCount values for m ≤ 4, sector sums = dpCount
  - General: sectorCount_zero_eq_one — for all m n, sectorCount m n 0 = 1
  - k=1 formula verified computationally for m ≤ 4
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi

namespace CausalAlgebraicGeometry.SectorDecomposition

/-! ## Row interval type (shared with DPVerifier) -/

/-- A row choice: either empty (none) or an interval [L, R] with L ≤ R. -/
abbrev RowChoice (n : ℕ) := Option (Fin n × Fin n)

/-- All valid row interval choices for [n]: none, or (L, R) with L ≤ R. -/
def rowChoices (n : ℕ) : Finset (RowChoice n) :=
  {none} ∪ (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2)).image some

/-- Check the convexity constraint for a pair of active rows. -/
def checkPairOK {m n : ℕ} (profile : Fin m → RowChoice n)
    (i₁ i₂ : Fin m) (L₁ R₁ L₂ R₂ : Fin n) : Bool :=
  if L₁ ≤ R₂ then
    decide (R₂ ≤ R₁) && decide (L₂ ≤ L₁) &&
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

/-! ## Block counting -/

/-- Whether a row is active (nonempty) in a profile. -/
def rowActive {m n : ℕ} (profile : Fin m → RowChoice n) (i : Fin m) : Bool :=
  (profile i).isSome

/-- Whether row i starts a new block: it is active, and either i = 0 or row i-1 is inactive. -/
def isBlockStart {m n : ℕ} (profile : Fin m → RowChoice n) (i : Fin m) : Bool :=
  rowActive profile i &&
  if h : i.val = 0 then true
  else !rowActive profile ⟨i.val - 1, by omega⟩

/-- Count the number of maximal contiguous runs of nonempty rows. -/
def numBlocks {m n : ℕ} (profile : Fin m → RowChoice n) : ℕ :=
  ((List.finRange m).filter (isBlockStart profile)).length

/-! ## Sector count and solid count -/

/-- The set of all valid convex profiles for [m]×[n]. -/
def validProfiles (m n : ℕ) : Finset (Fin m → RowChoice n) :=
  Fintype.piFinset (fun (_ : Fin m) => rowChoices n) |>.filter
    (fun p => isValidProfile p)

/-- Number of convex subsets of [m]×[n] with exactly k blocks. -/
def sectorCount (m n : ℕ) (k : ℕ) : ℕ :=
  (validProfiles m n |>.filter (fun p => numBlocks p == k)).card

/-- Number of convex subsets of [m]×[n] with ALL rows nonempty (solid block). -/
def solidCount (m n : ℕ) : ℕ :=
  (validProfiles m n |>.filter (fun p =>
    (List.finRange m).all (fun i => rowActive p i))).card

/-! ## Computational verification: m = 1 -/

theorem dpCount_1_1 : dpCount 1 1 = 2 := by native_decide
theorem sectorCount_1_0 : sectorCount 1 1 0 = 1 := by native_decide
theorem sectorCount_1_1 : sectorCount 1 1 1 = 1 := by native_decide
theorem sector_sum_1 : sectorCount 1 1 0 + sectorCount 1 1 1 = dpCount 1 1 := by native_decide

/-! ## Computational verification: m = 2 -/

theorem dpCount_2_2 : dpCount 2 2 = 13 := by native_decide
theorem sectorCount_2_0 : sectorCount 2 2 0 = 1 := by native_decide
theorem sectorCount_2_1 : sectorCount 2 2 1 = 12 := by native_decide
theorem sectorCount_2_2 : sectorCount 2 2 2 = 0 := by native_decide
theorem sector_sum_2 :
    sectorCount 2 2 0 + sectorCount 2 2 1 + sectorCount 2 2 2 = dpCount 2 2 := by
  native_decide

/-! ## Computational verification: m = 3 -/

theorem dpCount_3_3 : dpCount 3 3 = 114 := by native_decide
theorem sectorCount_3_0 : sectorCount 3 3 0 = 1 := by native_decide
theorem sectorCount_3_1 : sectorCount 3 3 1 = 108 := by native_decide
theorem sectorCount_3_2 : sectorCount 3 3 2 = 5 := by native_decide
theorem sectorCount_3_3 : sectorCount 3 3 3 = 0 := by native_decide
theorem sector_sum_3 :
    sectorCount 3 3 0 + sectorCount 3 3 1 + sectorCount 3 3 2 + sectorCount 3 3 3
    = dpCount 3 3 := by
  native_decide

/-! ## Solid count verification -/

theorem solidCount_1_1 : solidCount 1 1 = 1 := by native_decide
theorem solidCount_1_2 : solidCount 1 2 = 3 := by native_decide
theorem solidCount_1_3 : solidCount 1 3 = 6 := by native_decide
theorem solidCount_2_2 : solidCount 2 2 = 6 := by native_decide
theorem solidCount_2_3 : solidCount 2 3 = 20 := by native_decide
theorem solidCount_3_3 : solidCount 3 3 = 50 := by native_decide

/-! ## k=1 formula verification

  For a single-block convex subset of [m]×[m], the block has some height h (1 ≤ h ≤ m)
  and starts at some row r (0 ≤ r ≤ m-h). The number of solid convex subsets of
  [h]×[m] gives the choices for the block contents. So:

    sectorCount m m 1 = Σ h=1..m, (m - h + 1) * solidCount h m
-/

/-- Formula for k=1: sum over block heights. -/
def sectorCount1Formula (m : ℕ) : ℕ :=
  (List.range m).foldl (fun acc h =>
    acc + (m - (h + 1) + 1) * solidCount (h + 1) m) 0

theorem sectorCount1_formula_1 : sectorCount1Formula 1 = sectorCount 1 1 1 := by native_decide
theorem sectorCount1_formula_2 : sectorCount1Formula 2 = sectorCount 2 2 1 := by native_decide
theorem sectorCount1_formula_3 : sectorCount1Formula 3 = sectorCount 3 3 1 := by native_decide

/-! ## General theorem: sectorCount m n 0 = 1

  The only convex subset with 0 blocks is the empty set (all rows inactive).
  We prove this for all m and n by showing:
  1. The all-none profile is valid and has 0 blocks
  2. Any profile with 0 blocks must be the all-none profile
-/

/-- The empty profile: every row is inactive. -/
def emptyProfile (m n : ℕ) : Fin m → RowChoice n := fun _ => none

/-- isBlockStart is false for all rows in the empty profile. -/
theorem isBlockStart_emptyProfile (m n : ℕ) (i : Fin m) :
    isBlockStart (emptyProfile m n) i = false := by
  simp [isBlockStart, rowActive, emptyProfile]

/-- The empty profile has 0 blocks. -/
theorem numBlocks_emptyProfile (m n : ℕ) : numBlocks (emptyProfile m n) = 0 := by
  simp only [numBlocks]
  suffices h : (List.finRange m).filter (isBlockStart (emptyProfile m n)) = [] by
    simp [h]
  rw [List.filter_eq_nil_iff]
  intro i _
  simp [isBlockStart_emptyProfile]

/-- If a row is active, there exists a block-start row at or before it.
    Proved by strong induction: walk backwards from i to find the first active row. -/
private theorem exists_blockStart_le {m n : ℕ} (profile : Fin m → RowChoice n)
    (i : ℕ) (hi_lt : i < m) (hi : rowActive profile ⟨i, hi_lt⟩ = true) :
    ∃ j : Fin m, j.val ≤ i ∧ isBlockStart profile j = true := by
  induction i with
  | zero =>
    refine ⟨⟨0, hi_lt⟩, le_refl _, ?_⟩
    simp [isBlockStart, hi]
  | succ n ih =>
    by_cases hprev : rowActive profile ⟨n, by omega⟩ = true
    · obtain ⟨j, hj_le, hj_start⟩ := ih (by omega) hprev
      exact ⟨j, by omega, hj_start⟩
    · -- row n is inactive, so row n+1 starts a new block
      refine ⟨⟨n + 1, hi_lt⟩, le_refl _, ?_⟩
      simp only [isBlockStart, Bool.and_eq_true]
      refine ⟨hi, ?_⟩
      simp only [show n + 1 ≠ 0 from by omega, ↓reduceDIte, Bool.not_eq_true']
      simp only [Bool.not_eq_true] at hprev
      convert hprev using 2

/-- Any profile with numBlocks = 0 has all rows inactive. -/
theorem allInactive_of_numBlocks_zero {m n : ℕ} (profile : Fin m → RowChoice n)
    (h : numBlocks profile = 0) (i : Fin m) : profile i = none := by
  by_contra hne
  -- Row i is active
  have hi_active : rowActive profile i = true := by
    simp only [rowActive, Option.isSome]
    cases hpi : profile i with
    | none => exact absurd hpi hne
    | some _ => rfl
  -- So there exists a block start ≤ i
  obtain ⟨j, _, hj_start⟩ := exists_blockStart_le profile i.val i.isLt hi_active
  -- But numBlocks = 0 means no block starts exist
  simp only [numBlocks] at h
  have hj_mem : j ∈ (List.finRange m).filter (isBlockStart profile) := by
    simp [List.mem_filter, List.mem_finRange]
    exact hj_start
  have hempty := List.length_eq_zero_iff.mp h
  rw [hempty] at hj_mem
  simp at hj_mem

/-- The empty profile is the unique profile with 0 blocks. -/
theorem eq_emptyProfile_of_numBlocks_zero {m n : ℕ} (profile : Fin m → RowChoice n)
    (h : numBlocks profile = 0) : profile = emptyProfile m n :=
  funext (fun i => allInactive_of_numBlocks_zero profile h i)

/-- The empty profile is valid (it defines the empty convex set). -/
theorem isValidProfile_emptyProfile (m n : ℕ) : isValidProfile (emptyProfile m n) = true := by
  simp only [isValidProfile, emptyProfile]
  simp [List.all_eq_true]

/-- The empty profile is in validProfiles. -/
theorem emptyProfile_mem_validProfiles (m n : ℕ) :
    emptyProfile m n ∈ validProfiles m n := by
  simp only [validProfiles, Finset.mem_filter]
  refine ⟨?_, isValidProfile_emptyProfile m n⟩
  simp only [Fintype.mem_piFinset, emptyProfile]
  intro _
  simp [rowChoices]

/-- **General theorem**: sectorCount m n 0 = 1 for all m, n.
    Only the empty set has 0 blocks. -/
theorem sectorCount_zero_eq_one (m n : ℕ) : sectorCount m n 0 = 1 := by
  simp only [sectorCount]
  rw [show 1 = Finset.card {emptyProfile m n} from by simp]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_singleton, beq_iff_eq]
  constructor
  · intro ⟨_, hp_blocks⟩
    exact eq_emptyProfile_of_numBlocks_zero p hp_blocks
  · intro hp
    subst hp
    exact ⟨emptyProfile_mem_validProfiles m n, numBlocks_emptyProfile m n⟩

/-! ## Computational verification: m = 4 -/

theorem dpCount_4_4 : dpCount 4 4 = 1146 := by native_decide
theorem sectorCount_4_0 : sectorCount 4 4 0 = 1 := by native_decide
theorem sectorCount_4_1 : sectorCount 4 4 1 = 1030 := by native_decide
theorem sectorCount_4_2 : sectorCount 4 4 2 = 115 := by native_decide
theorem sectorCount_4_3 : sectorCount 4 4 3 = 0 := by native_decide
theorem sectorCount_4_4 : sectorCount 4 4 4 = 0 := by native_decide
theorem sector_sum_4 :
    sectorCount 4 4 0 + sectorCount 4 4 1 + sectorCount 4 4 2 +
    sectorCount 4 4 3 + sectorCount 4 4 4 = dpCount 4 4 := by
  native_decide

theorem solidCount_4_4 : solidCount 4 4 = 490 := by native_decide

theorem sectorCount1_formula_4 : sectorCount1Formula 4 = sectorCount 4 4 1 := by native_decide

/-! ## Summary of sector decomposition data

  Sector counts sectorCount m m k:
    m=1: [1, 1]                         sum = 2
    m=2: [1, 12, 0]                     sum = 13
    m=3: [1, 108, 5, 0]                 sum = 114
    m=4: [1, 1030, 115, 0, 0]           sum = 1146

  Solid counts (all rows nonempty) solidCount m m:
    solidCount 1 1 = 1
    solidCount 2 2 = 6
    solidCount 3 3 = 50
    solidCount 4 4 = 490

  k=1 formula (verified for m ≤ 4):
    sectorCount m m 1 = Σ_{h=1}^{m} (m-h+1) · solidCount h m
-/

end CausalAlgebraicGeometry.SectorDecomposition
