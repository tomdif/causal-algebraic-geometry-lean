/-
  AntitoneCount.lean — Stars-and-bars: antitone functions Fin m → Fin (n+1) counted by C(m+n,m)
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.AntitoneCount

open Finset Nat

/-! ## Equiv between antitone functions Fin m → Fin (n+1) and Sigma fiber -/

/-- The subtype of antitone functions. -/
abbrev AntiFun (m n : ℕ) := {f : Fin m → Fin (n + 1) // Antitone f}

/-- The sigma type: choice of head value k, then antitone tail into Fin (k+1). -/
abbrev AntiSigma (m n : ℕ) := (k : Fin (n + 1)) × AntiFun m k.val

/-- Forward: extract head and restrict tail. -/
def fwd (m n : ℕ) : AntiFun (m + 1) n → AntiSigma m n :=
  fun ⟨f, hf⟩ =>
    ⟨f 0,
     ⟨fun i => ⟨(f i.succ).val, Nat.lt_succ_of_le (hf (Fin.zero_le i.succ))⟩,
      fun i j hij => by
        simp only [Fin.le_def]
        exact hf (Fin.succ_le_succ_iff.mpr hij)⟩⟩

/-- Backward: cons head onto embedded tail. -/
def bwd (m n : ℕ) : AntiSigma m n → AntiFun (m + 1) n :=
  fun ⟨k, g, hg⟩ =>
    let f : Fin (m + 1) → Fin (n + 1) :=
      Fin.cons k (fun i => ⟨(g i).val, lt_of_lt_of_le (g i).isLt (Nat.succ_le_of_lt k.isLt)⟩)
    ⟨f, by
      intro i j hij
      show f j ≤ f i
      match i, j with
      | ⟨0, _⟩, ⟨0, _⟩ => exact le_rfl
      | ⟨0, _⟩, ⟨j' + 1, hj'⟩ =>
        show f ⟨j' + 1, hj'⟩ ≤ f ⟨0, _⟩
        simp only [f, Fin.le_def]
        exact Nat.le_of_lt_succ (g ⟨j', Nat.lt_of_succ_lt_succ hj'⟩).isLt
      | ⟨i' + 1, _⟩, ⟨0, _⟩ =>
        simp [Fin.le_def] at hij
      | ⟨i' + 1, hi'⟩, ⟨j' + 1, hj'⟩ =>
        show f ⟨j' + 1, hj'⟩ ≤ f ⟨i' + 1, hi'⟩
        simp only [f, Fin.le_def]
        exact hg (by simp [Fin.le_def] at hij ⊢; omega)⟩

/-- fwd and bwd are inverse (right). -/
theorem fwd_bwd (m n : ℕ) (x : AntiSigma m n) : fwd m n (bwd m n x) = x := by
  obtain ⟨k, g, hg⟩ := x
  simp only [fwd, bwd]
  refine Sigma.ext rfl ?_
  simp only [heq_eq_eq]
  ext i
  simp [Fin.cons_succ]

/-- fwd and bwd are inverse (left). -/
theorem bwd_fwd (m n : ℕ) (x : AntiFun (m + 1) n) : bwd m n (fwd m n x) = x := by
  obtain ⟨f, hf⟩ := x
  simp only [fwd, bwd]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [Fin.cons_zero]
  · simp [Fin.cons_succ]

/-- Equiv between AntiFun (m+1) n and AntiSigma m n. -/
def antiEquiv (m n : ℕ) : AntiFun (m + 1) n ≃ AntiSigma m n where
  toFun := fwd m n
  invFun := bwd m n
  left_inv := bwd_fwd m n
  right_inv := fwd_bwd m n

/-! ## Card computation via Fintype -/

-- Link Finset.card of filter to Fintype.card of subtype
lemma filter_card_eq_fintype_card (m n : ℕ) :
    ((univ : Finset (Fin m → Fin (n + 1))).filter Antitone).card =
    Fintype.card (AntiFun m n) :=
  (Fintype.card_subtype _).symm

-- Helper: sum of multichoose over Fin (n+1)
private lemma sum_multichoose_eq (m n : ℕ) :
    ∑ k : Fin (n + 1), Nat.multichoose (↑k + 1) m = Nat.multichoose (n + 1) (m + 1) := by
  induction n with
  | zero => simp [Finset.univ_unique]
  | succ n' ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, ← Nat.multichoose_succ_succ]

-- Main induction
theorem card_antitone_eq_multichoose :
    ∀ (m n : ℕ), Fintype.card (AntiFun m n) = Nat.multichoose (n + 1) m := by
  intro m
  induction m with
  | zero =>
    intro n
    -- Fin 0 → Fin (n+1) has one element, which is vacuously antitone
    have : Unique (Fin 0 → Fin (n + 1)) := Pi.uniqueOfIsEmpty _
    have : Unique (AntiFun 0 n) := by
      refine ⟨⟨⟨default, fun i => Fin.elim0 i⟩⟩, ?_⟩
      intro ⟨f, _⟩
      congr 1
      funext i; exact Fin.elim0 i
    simp [Fintype.card_unique]
  | succ m ih =>
    intro n
    -- Use the equiv to get the sigma decomposition
    rw [Fintype.card_congr (antiEquiv m n)]
    simp only [AntiSigma, Fintype.card_sigma]
    simp_rw [ih]
    exact sum_multichoose_eq m n

-- Final theorem
theorem card_antitone_eq_choose (m n : ℕ) :
    ((univ : Finset (Fin m → Fin (n + 1))).filter Antitone).card =
    Nat.choose (m + n) m := by
  rw [filter_card_eq_fintype_card, card_antitone_eq_multichoose, Nat.multichoose_eq]
  congr 1
  omega

end CausalAlgebraicGeometry.AntitoneCount
