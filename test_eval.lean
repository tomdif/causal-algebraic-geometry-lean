import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

-- Efficient count of dominating pairs
def antitoneFunsOf (m : ℕ) : Finset (Fin m → Fin m) :=
  Finset.univ.filter Antitone

def efficientDomCount (m : ℕ) : ℕ :=
  (antitoneFunsOf m).sum (fun g => ((antitoneFunsOf m).filter (fun u => ∀ i, u i ≤ g i)).card)

#eval efficientDomCount 0
#eval efficientDomCount 1
#eval efficientDomCount 2
#eval efficientDomCount 3
#eval efficientDomCount 4
#eval efficientDomCount 5
#eval Nat.choose (2 * 0) 0 ^ 2 / (2 * (0 + 1))
#eval Nat.choose (2 * 1) 1 ^ 2 / (2 * (1 + 1))
#eval Nat.choose (2 * 2) 2 ^ 2 / (2 * (2 + 1))
#eval Nat.choose (2 * 3) 3 ^ 2 / (2 * (3 + 1))
#eval Nat.choose (2 * 4) 4 ^ 2 / (2 * (4 + 1))
#eval Nat.choose (2 * 5) 5 ^ 2 / (2 * (5 + 1))
