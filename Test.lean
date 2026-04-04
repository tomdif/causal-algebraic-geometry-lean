import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Test

def traceRK (m : ℕ) : ℕ := (m / 2) ^ 2
def traceK (m : ℕ) : ℕ := m * (m - 1) / 2
def traceEven (m : ℕ) : ℕ := (traceK m + traceRK m) / 2
def traceOdd (m : ℕ) : ℕ := (traceK m - traceRK m) / 2

-- Strategy: use Nat.div_add_mod, show divisibility, then multiply both sides
-- Key insight: show the numerator is even, so /2 * 2 = numerator

-- Helper: for n ≥ 2, 2*n*(2*n-1)/2 = n*(2*n-1)
-- And (n*(2*n-1) + n^2) is even because n*(2n-1) + n^2 = n*(3n-1) which is even for all n

-- Actually, let me just try the brute force approach with sufficient lemmas
theorem trace_even_m2n (n : ℕ) (hn : 2 ≤ n) :
    traceEven (2 * n) * 2 = n * (3 * n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- n = k + 2
  simp only [traceEven, traceK, traceRK]
  -- Simplify 2*(k+2) / 2 = k+2
  have h1 : 2 * (k + 2) / 2 = k + 2 := Nat.mul_div_cancel_left _ (by norm_num)
  rw [h1]
  -- Simplify 2*(k+2) - 1
  have h2 : 2 * (k + 2) - 1 = 2 * k + 3 := by ring_nf; simp [Nat.add_sub_cancel]
  rw [h2]
  -- Simplify 2*(k+2) * (2*k+3) / 2
  have h3 : 2 * (k + 2) * (2 * k + 3) / 2 = (k + 2) * (2 * k + 3) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [h3]
  -- Now goal: ((k+2)*(2*k+3) + (k+2)^2) / 2 * 2 = (k+2) * (3*(k+2) - 1)
  -- RHS = (k+2) * (3*k+5)
  -- LHS numerator = (k+2)*((2k+3) + (k+2)) = (k+2)*(3k+5)
  -- (k+2)*(3k+5) is even? Not necessarily... but (k+2)*(3k+5)/2 * 2 = (k+2)*(3k+5) when it's even
  -- Actually (k+2)*(3k+5): when k is even, 3k+5 is odd, k+2 is even. When k is odd, 3k+5 is even.
  -- So always even. Good.
  have h4 : (k + 2) * (2 * k + 3) + (k + 2) ^ 2 = (k + 2) * (3 * k + 5) := by ring
  rw [h4]
  have h5 : 3 * (k + 2) - 1 = 3 * k + 5 := by ring_nf; simp [Nat.add_sub_cancel]
  rw [h5]
  -- Goal: (k+2) * (3*k+5) / 2 * 2 = (k+2) * (3*k+5)
  exact Nat.div_mul_cancel (by
    -- Need: 2 ∣ (k+2)*(3*k+5)
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- k = 2j, k+2 = 2j+2 = 2*(j+1)
      subst hj; exact ⟨(j + 1) * (3 * (2 * j) + 5), by ring⟩
    · -- k = 2j+1, 3k+5 = 6j+8 = 2*(3j+4)
      subst hj; exact ⟨(2 * j + 3) * (3 * j + 4), by ring⟩)

end Test
