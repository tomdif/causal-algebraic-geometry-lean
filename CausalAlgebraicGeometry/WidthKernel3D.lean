/-
  Width Kernel Normalization for the d=3 Spectral Theory (Theorem A, discrete)

  At each slice position, the state is (a, b) with 0 ≤ a, b ≤ m-1.
  Width w = b - a + 1 if b ≥ a, else 0.

  The transition (a, b) → (a', b') with a' ≤ a, b' ≤ b produces:
  - Zero width if b' < a'
  - Positive width w' = b' - a' + 1 if b' ≥ a'

  Total transitions from (a, b) = (a+1)(b+1) (rectangle [0,a]×[0,b]).

  Normalization: zeroWidthCount + positiveWidthCount = (a+1)(b+1).

  This is the discrete version of Theorem A: P(0|s) + ∫K ds' = 1.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace WidthKernel3D

/-- Zero-width transitions: pairs (a', b') with a' ≤ a, b' ≤ b, b' < a'. -/
def zeroWidth (a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (a + 1) ×ˢ Finset.range (b + 1)).filter (fun p => p.2 < p.1)

/-- Positive-width transitions: pairs (a', b') with a' ≤ a, b' ≤ b, a' ≤ b'. -/
def posWidth (a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (a + 1) ×ˢ Finset.range (b + 1)).filter (fun p => p.1 ≤ p.2)

/-- Normalization: zero + positive = total = (a+1)(b+1). -/
theorem kernel_normalization (a b : ℕ) :
    (zeroWidth a b).card + (posWidth a b).card = (a + 1) * (b + 1) := by
  -- The two sets are disjoint and their union is the full rectangle
  have hDisjoint : Disjoint (zeroWidth a b) (posWidth a b) := by
    rw [Finset.disjoint_left]
    intro ⟨x, y⟩ hZ hP
    simp only [zeroWidth, posWidth, Finset.mem_filter] at hZ hP
    omega
  have hUnion : zeroWidth a b ∪ posWidth a b =
      Finset.range (a + 1) ×ˢ Finset.range (b + 1) := by
    ext ⟨x, y⟩
    simp only [zeroWidth, posWidth, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product, Finset.mem_range]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h; by_cases hxy : y < x <;> [left; right] <;> exact ⟨h, by omega⟩
  rw [← Finset.card_union_of_disjoint hDisjoint, hUnion,
      Finset.card_product, Finset.card_range, Finset.card_range]

/-- Verified instances of zero-width count for small a. -/
theorem zwc_0_0 : (zeroWidth 0 0).card = 0 := by decide
theorem zwc_1_1 : (zeroWidth 1 1).card = 1 := by decide
theorem zwc_2_2 : (zeroWidth 2 2).card = 3 := by decide
theorem zwc_3_3 : (zeroWidth 3 3).card = 6 := by decide
theorem zwc_4_4 : (zeroWidth 4 4).card = 10 := by decide
theorem zwc_2_5 : (zeroWidth 2 5).card = 3 := by decide
theorem zwc_3_7 : (zeroWidth 3 7).card = 6 := by decide

-- The positive-width count when a ≤ b: (a+1)(b+1) - a(a+1)/2.
-- Follows from kernel_normalization + zero_width_count_pos_slab.

end WidthKernel3D
