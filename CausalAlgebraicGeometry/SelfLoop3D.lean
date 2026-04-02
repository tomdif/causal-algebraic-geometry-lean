/-
  Self-Loop Identity for the d=3 Width Chain (Theorem B, general)

  2 × |{(a',b') ∈ [0..b+1]×[0..b] : b' < a'}| = (b+2)(b+1) for all b.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace SelfLoop3D

/-- Z(b) = {(a', b') ∈ [0..b+1]×[0..b] : b' < a'}. -/
abbrev Z (b : ℕ) := (Finset.range (b + 2) ×ˢ Finset.range (b + 1)).filter
  (fun p : ℕ × ℕ => p.2 < p.1)

/-- |Z(b)| = Σ_{a'=0}^{b+1} a'. -/
theorem Z_card (b : ℕ) : (Z b).card = (Finset.range (b + 2)).sum id := by
  -- Decompose by first coordinate: Z = ⊔_{a'} {a'} × {b' < a', b' ≤ b}
  have hdecomp : Z b = (Finset.range (b + 2)).biUnion (fun a' =>
    ({a'} ×ˢ (Finset.range (min a' (b + 1))))) := by
    ext ⟨x, y⟩
    simp only [Z, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_biUnion, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hx, hy⟩, hlt⟩
      exact ⟨x, hx, rfl, by omega⟩
    · rintro ⟨a', ha', rfl, hy⟩
      exact ⟨⟨ha', by omega⟩, by omega⟩
  rw [hdecomp, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro a' ha'
    simp only [Finset.mem_range] at ha'
    simp only [Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul, id]
    exact Nat.min_eq_left (by omega)
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
    intro ⟨x, y⟩ ⟨rfl, _⟩ ⟨h, _⟩
    exact hij h

/-- THEOREM B (general): 2|Z(b)| = (b+2)(b+1) for all b ∈ ℕ. -/
theorem self_loop_half (b : ℕ) :
    2 * (Z b).card = (b + 2) * (b + 1) := by
  rw [Z_card]
  -- 2 * Σ_{i=0}^{b+1} i = (b+2)(b+1)
  -- Use Mathlib: Finset.sum_range_id_mul_two n : (Σ i ∈ range n, i) * 2 = n * (n - 1)
  have h := Finset.sum_range_id_mul_two (b + 2)
  -- h : (Σ i ∈ range(b+2), i) * 2 = (b+2) * (b+2-1) = (b+2)*(b+1)
  simp only [id] at h ⊢
  -- h : (Finset.range (b + 2)).sum (·) * 2 = (b + 2) * (b + 1)
  -- goal : 2 * (Finset.range (b + 2)).sum (·) = (b + 2) * (b + 1)
  have : b + 2 - 1 = b + 1 := by omega
  rw [this] at h
  linarith [mul_comm ((Finset.range (b + 2)).sum (·)) 2]

end SelfLoop3D
