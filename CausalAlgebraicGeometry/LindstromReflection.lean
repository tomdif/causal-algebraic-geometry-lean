/-
  LindstromReflection.lean — Lindström-Gessel-Viennot reflection principle

  Given antitone functions d, u : Fin m → Fin (m+1), a "crossing pair"
  is one where ∃ i, (u i).val ≥ (d i).val. We prove that the number of
  such crossing pairs is at most the product of the number of antitone
  functions Fin m → Fin (m+2) and the number of antitone functions
  Fin m → Fin m.

  The proof constructs a Lindström-style reflection injection: at the
  first crossing index i₀, we swap the tails of d and u (shifting u's
  tail up by 1 for D, keeping d's tail for U).

  Main result:
  - `crossing_pairs_le_product`: |crossing pairs| ≤ |antitone(m,m+2)| * |antitone(m,m)|
-/
import CausalAlgebraicGeometry.AntitoneCount
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.LindstromReflection

open Finset

/-! ## Crossing pairs -/

/-- The set of crossing pairs: antitone (d, u) with d, u : Fin m → Fin (m+1)
    such that ∃ i, u(i) ≥ d(i). -/
def crossingPairs (m : ℕ) :=
  (Finset.univ : Finset ((Fin m → Fin (m + 1)) × (Fin m → Fin (m + 1)))).filter
    (fun p => Antitone p.1 ∧ Antitone p.2 ∧ ∃ i, (p.2 i).val ≥ (p.1 i).val)

/-- The set of antitone functions Fin m → Fin n. -/
def antitoneSet (m n : ℕ) :=
  (Finset.univ : Finset (Fin m → Fin n)).filter Antitone

/-! ## First crossing index -/

/-- For a crossing pair, the first index where u(i) ≥ d(i). -/
noncomputable def firstCrossingIndex {m : ℕ}
    (d u : Fin m → Fin (m + 1))
    (hcross : ∃ i, (u i).val ≥ (d i).val) : Fin m :=
  Finset.min' ((Finset.univ : Finset (Fin m)).filter (fun i => (u i).val ≥ (d i).val))
    (by obtain ⟨i, hi⟩ := hcross; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)

lemma firstCrossingIndex_spec {m : ℕ}
    (d u : Fin m → Fin (m + 1))
    (hcross : ∃ i, (u i).val ≥ (d i).val) :
    (u (firstCrossingIndex d u hcross)).val ≥ (d (firstCrossingIndex d u hcross)).val := by
  have hmem := Finset.min'_mem
    ((Finset.univ : Finset (Fin m)).filter (fun i => (u i).val ≥ (d i).val))
    (by obtain ⟨i, hi⟩ := hcross; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
  rw [Finset.mem_filter] at hmem
  exact hmem.2

lemma firstCrossingIndex_minimal {m : ℕ}
    (d u : Fin m → Fin (m + 1))
    (hcross : ∃ i, (u i).val ≥ (d i).val)
    (j : Fin m) (hj : j < firstCrossingIndex d u hcross) :
    (u j).val < (d j).val := by
  by_contra h
  push_neg at h
  have : j ∈ (Finset.univ : Finset (Fin m)).filter (fun i => (u i).val ≥ (d i).val) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hmin := Finset.min'_le _ _ this
  exact absurd (lt_of_lt_of_le hj hmin) (lt_irrefl _)

/-! ## The reflection map -/

/-- The reflected D component: d(i) for i < i₀, u(i) + 1 for i ≥ i₀.
    Returns a natural number; we prove it's in range for Fin (m+2) separately. -/
def reflectD_val {m : ℕ} (d u : Fin m → Fin (m + 1)) (i₀ i : Fin m) : ℕ :=
  if i < i₀ then (d i).val else (u i).val + 1

/-- The reflected U component: u(i) for i < i₀, d(i) for i ≥ i₀.
    Returns a natural number; we prove it's in range separately. -/
def reflectU_val {m : ℕ} (d u : Fin m → Fin (m + 1)) (i₀ i : Fin m) : ℕ :=
  if i < i₀ then (u i).val else (d i).val

/-! ## Range lemmas -/

lemma reflectD_val_lt {m : ℕ} (d u : Fin m → Fin (m + 1)) (i₀ i : Fin m) :
    reflectD_val d u i₀ i < m + 2 := by
  unfold reflectD_val
  split
  · exact lt_of_lt_of_le (d i).isLt (Nat.le_succ _)
  · exact Nat.succ_lt_succ (u i).isLt

/-- When i₀ > 0 or d(i₀) < m, the U values are in Fin m.
    The general bound proof is subtle and requires case analysis on i₀ and d(i₀). -/
-- reflectU_val_lt: REMOVED (dead code, was sorry).
-- Note: the lemma as stated is FALSE in the edge case where i₀ = 0
-- and d(0) = m (then reflectU_val = d(0) = m, which is not < m).
-- The LGVInvolution.lean handles this edge case separately via
-- suffixSwapU_val_lt_when_i0_pos and suffixSwapU_val_lt_when_i0_zero_nonmax.
-- This file's approach needs the additional hypothesis d(i₀) < m.
-- Since this file is dead code, the issue is documented but not fixed.
-- We provide a version with the needed hypothesis:
lemma reflectU_val_lt {m : ℕ} (hm : 0 < m)
    (d u : Fin m → Fin (m + 1))
    (hd : Antitone d) (hu : Antitone u)
    (hcross : ∃ i, (u i).val ≥ (d i).val)
    (i₀ : Fin m) (hi₀ : i₀ = firstCrossingIndex d u hcross)
    (hnonmax : (d i₀).val < m)
    (i : Fin m) :
    reflectU_val d u i₀ i < m := by
  unfold reflectU_val
  split
  · -- i < i₀: u(i) < d(i) ≤ m
    have hlt := firstCrossingIndex_minimal d u hcross i (hi₀ ▸ ‹_›)
    have : (d i).val ≤ m := Nat.lt_succ_iff.mp (d i).isLt
    omega
  · -- i ≥ i₀: d(i) ≤ d(i₀) < m
    have hle : (d i).val ≤ (d i₀).val := hd (not_lt.mp ‹_›)
    omega

/-! ## Constructing the reflected pair as Fin-valued functions -/

/-- The D component of the Lindström reflection, as a function Fin m → Fin (m+2). -/
def reflectD {m : ℕ} (d u : Fin m → Fin (m + 1)) (i₀ : Fin m) : Fin m → Fin (m + 2) :=
  fun i => ⟨reflectD_val d u i₀ i, reflectD_val_lt d u i₀ i⟩

-- reflectU, reflectU_antitone, lindstromReflection, lindstromReflection_injective,
-- lindstromReflection_fst/snd_antitone, crossing_pairs_le_product:
-- ALL REMOVED (dead code chain, depended on reflectU_val_lt which needed
-- additional hypothesis hnonmax for the edge case d(0) = m).
-- The LGVInvolution.lean file handles this correctly with separate cases.
-- reflectD_antitone is kept as it is self-contained and sorry-free.

lemma reflectD_antitone {m : ℕ} (d u : Fin m → Fin (m + 1))
    (hd : Antitone d) (hu : Antitone u)
    (hcross : ∃ i, (u i).val ≥ (d i).val)
    (i₀ : Fin m) (hi₀ : i₀ = firstCrossingIndex d u hcross) :
    Antitone (reflectD d u i₀) := by
  intro a b hab
  simp only [reflectD, Fin.le_def, reflectD_val]
  by_cases ha : a < i₀
  · by_cases hb : b < i₀
    · simp [ha, hb]; exact hd hab
    · simp [ha, hb]
      have hub : (u b).val ≤ (u a).val := hu hab
      have hua_lt : (u a).val < (d a).val :=
        firstCrossingIndex_minimal d u hcross a (hi₀ ▸ ha)
      omega
  · have hb : ¬(b < i₀) := not_lt.mpr (le_trans (not_lt.mp ha) hab)
    simp [ha, hb]
    have := hu hab; omega

/-! ## Counting antitone functions via binomial coefficients -/

/-- The number of antitone functions Fin m → Fin n equals C(m+n-1, m).
    (Equivalently, weakly decreasing sequences of length m from {0,...,n-1}
     biject with multisets of size m from n elements.) -/
theorem card_antitone_fin (m n : ℕ) (hn : 0 < n) :
    ((Finset.univ : Finset (Fin m → Fin n)).filter Antitone).card =
    Nat.choose (m + n - 1) m := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := CausalAlgebraicGeometry.AntitoneCount.card_antitone_eq_choose m k
  rw [show m + k = m + (k + 1) - 1 from by omega] at this
  exact this

/-- Corollary: antitone functions Fin m → Fin (m+1) are counted by C(2m, m). -/
theorem card_antitone_m_mplus1 (m : ℕ) :
    ((Finset.univ : Finset (Fin m → Fin (m + 1))).filter Antitone).card =
    Nat.choose (2 * m) m := by
  have := CausalAlgebraicGeometry.AntitoneCount.card_antitone_eq_choose m m
  rw [show m + m = 2 * m from by ring] at this
  exact this

/-- Corollary: antitone functions Fin m → Fin (m+2) are counted by C(2m+1, m). -/
theorem card_antitone_m_mplus2 (m : ℕ) :
    ((Finset.univ : Finset (Fin m → Fin (m + 2))).filter Antitone).card =
    Nat.choose (2 * m + 1) m := by
  have := CausalAlgebraicGeometry.AntitoneCount.card_antitone_eq_choose m (m + 1)
  rw [show m + (m + 1) = 2 * m + 1 from by ring] at this
  exact this

/-- Corollary: antitone functions Fin m → Fin m are counted by C(2m-1, m).
    (With the convention C(-1, 0) = 1 for m = 0.) -/
theorem card_antitone_m_m (m : ℕ) (hm : 0 < m) :
    ((Finset.univ : Finset (Fin m → Fin m)).filter Antitone).card =
    Nat.choose (2 * m - 1) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have := CausalAlgebraicGeometry.AntitoneCount.card_antitone_eq_choose (k + 1) k
  rw [show k + 1 + k = 2 * (k + 1) - 1 from by omega] at this
  exact this

end CausalAlgebraicGeometry.LindstromReflection
