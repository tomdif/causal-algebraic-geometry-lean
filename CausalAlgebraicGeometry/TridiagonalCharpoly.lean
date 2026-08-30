/-
  TridiagonalCharpoly.lean — Three-term recurrence for the characteristic
  polynomial of a symmetric tridiagonal matrix.

  Main result (`D_recurrence`): for `tridiag n a b : Matrix (Fin n) (Fin n) R`
  the symmetric tridiagonal matrix with diagonal `a 0, …, a (n-1)` and
  sub/super-diagonal `b 0, …, b (n-2)`, the sequence
  `D k := (tridiag k a b).charpoly` satisfies

      D (k+2) = (X - C (a (k+1))) * D (k+1) − C (b k) ^ 2 * D k.

  Proof: Laplace expansion of `det (charmatrix (tridiag (k+2) a b))` along
  the last row, then expansion of the off-diagonal cofactor's submatrix
  along ITS last column.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace CausalAlgebraicGeometry.TridiagonalCharpoly

open Matrix Polynomial Finset

variable {R : Type*} [CommRing R]

/-! ## Definitions -/

noncomputable def tridiag (n : ℕ) (a b : ℕ → R) :
    Matrix (Fin n) (Fin n) R := fun i j =>
  if i.val = j.val then a i.val
  else if i.val + 1 = j.val then b i.val
  else if j.val + 1 = i.val then b j.val
  else 0

noncomputable def D (a b : ℕ → R) (n : ℕ) : R[X] :=
  (tridiag n a b).charpoly

/-! ## Charmatrix entries -/

lemma charmatrix_tridiag_apply (n : ℕ) (a b : ℕ → R) (i j : Fin n) :
    charmatrix (tridiag n a b) i j =
      if i = j then X - C (a i.val)
      else if i.val + 1 = j.val then -C (b i.val)
      else if j.val + 1 = i.val then -C (b j.val)
      else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, charmatrix_apply_eq]
    show X - C (tridiag n a b i i) = X - C (a i.val)
    congr 2
    simp [tridiag]
  · rw [charmatrix_apply_ne _ _ _ hij, if_neg hij]
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    show -C (tridiag n a b i j) = _
    simp only [tridiag, if_neg hval]
    split_ifs <;> simp

/-! ## Submatrix lemmas -/

lemma charmatrix_submatrix_castSucc (k : ℕ) (a b : ℕ → R) :
    (charmatrix (tridiag (k+2) a b)).submatrix
        (Fin.castSucc : Fin (k+1) → Fin (k+2))
        (Fin.castSucc : Fin (k+1) → Fin (k+2))
      = charmatrix (tridiag (k+1) a b) := by
  ext i j
  simp only [submatrix_apply]
  rw [charmatrix_tridiag_apply, charmatrix_tridiag_apply]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, if_pos rfl]; rfl
  · have h1 : (Fin.castSucc i : Fin (k+2)) ≠ (Fin.castSucc j : Fin (k+2)) :=
      fun h => hij (Fin.castSucc_injective _ h)
    rw [if_neg h1, if_neg hij]; rfl

lemma double_submatrix_eq (k : ℕ) (a b : ℕ → R) :
    ((charmatrix (tridiag (k+2) a b)).submatrix
        (Fin.castSucc : Fin (k+1) → Fin (k+2))
        ((Fin.castSucc (Fin.last k) : Fin (k+1)).succAbove)).submatrix
        (Fin.castSucc : Fin k → Fin (k+1))
        (Fin.castSucc : Fin k → Fin (k+1))
      = charmatrix (tridiag k a b) := by
  ext i j
  simp only [submatrix_apply]
  have hjlt : j.val < k := j.isLt
  have hcs_j_lt : (Fin.castSucc j : Fin (k+1)) < Fin.castSucc (Fin.last k) := by
    rw [Fin.lt_def]
    show j.val < (Fin.last k).val
    rw [Fin.val_last]; exact hjlt
  have hcol : (Fin.castSucc (Fin.last k) : Fin (k+1)).succAbove (Fin.castSucc j) =
              Fin.castSucc (Fin.castSucc j) :=
    Fin.succAbove_of_castSucc_lt _ _ hcs_j_lt
  rw [hcol, charmatrix_tridiag_apply, charmatrix_tridiag_apply]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, if_pos rfl]; rfl
  · have h1 : (Fin.castSucc (Fin.castSucc i) : Fin (k+2)) ≠
              (Fin.castSucc (Fin.castSucc j) : Fin (k+2)) :=
      fun h => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _ h))
    rw [if_neg h1, if_neg hij]; rfl

/-! ## Last-row entries -/

lemma last_row_diag (k : ℕ) (a b : ℕ → R) :
    (charmatrix (tridiag (k+2) a b)) (Fin.last (k+1)) (Fin.last (k+1)) =
      X - C (a (k+1)) := by
  rw [charmatrix_apply_eq]
  show X - C (tridiag (k+2) a b (Fin.last (k+1)) (Fin.last (k+1))) = X - C (a (k+1))
  congr 2
  simp [tridiag, Fin.val_last]

lemma last_row_subdiag (k : ℕ) (a b : ℕ → R) :
    (charmatrix (tridiag (k+2) a b)) (Fin.last (k+1)) (Fin.castSucc (Fin.last k)) =
      -C (b k) := by
  rw [charmatrix_tridiag_apply]
  have hL : (Fin.last (k+1) : Fin (k+2)).val = k+1 := Fin.val_last (k+1)
  have hcs : (Fin.castSucc (Fin.last k) : Fin (k+2)).val = k := by
    show (Fin.last k).val = k; exact Fin.val_last k
  have h1 : (Fin.last (k+1) : Fin (k+2)) ≠ Fin.castSucc (Fin.last k) := by
    intro heq
    have := congr_arg Fin.val heq
    rw [hL, hcs] at this; omega
  rw [if_neg h1]
  have h2 : ¬ (Fin.last (k+1) : Fin (k+2)).val + 1 =
              (Fin.castSucc (Fin.last k) : Fin (k+2)).val := by
    rw [hL, hcs]; omega
  rw [if_neg h2]
  have h3 : (Fin.castSucc (Fin.last k) : Fin (k+2)).val + 1 =
            (Fin.last (k+1) : Fin (k+2)).val := by
    rw [hL, hcs]
  rw [if_pos h3]
  congr 1
  exact hcs

lemma last_row_zero (k : ℕ) (a b : ℕ → R) (j : Fin (k+2))
    (h1 : j ≠ Fin.last (k+1)) (h2 : j ≠ Fin.castSucc (Fin.last k)) :
    (charmatrix (tridiag (k+2) a b)) (Fin.last (k+1)) j = 0 := by
  rw [charmatrix_tridiag_apply]
  rw [if_neg (fun h => h1 h.symm)]
  have hL : (Fin.last (k+1) : Fin (k+2)).val = k+1 := Fin.val_last (k+1)
  have hcs : (Fin.castSucc (Fin.last k) : Fin (k+2)).val = k := Fin.val_last k
  have hjvallt : j.val < k := by
    have hne1 : j.val ≠ k+1 := by
      intro heq; apply h1; ext; rw [hL]; exact heq
    have hne2 : j.val ≠ k := by
      intro heq; apply h2; ext; rw [hcs]; exact heq
    have := j.isLt; omega
  rw [if_neg (by rw [hL]; omega), if_neg (by rw [hL]; omega)]

/-! ## Inner submatrix last column -/

lemma inner_last_col_at_last (k : ℕ) (a b : ℕ → R) :
    (charmatrix (tridiag (k+2) a b)) (Fin.castSucc (Fin.last k))
        ((Fin.castSucc (Fin.last k) : Fin (k+1)).succAbove (Fin.last k)) = -C (b k) := by
  have hcol : (Fin.castSucc (Fin.last k) : Fin (k+1)).succAbove (Fin.last k) =
              Fin.last (k+1) := by
    rw [Fin.succAbove_castSucc_self]
    ext
    show (Fin.last k).succ.val = (Fin.last (k+1)).val
    simp [Fin.val_succ, Fin.val_last]
  rw [hcol, charmatrix_tridiag_apply]
  have hL : (Fin.last (k+1) : Fin (k+2)).val = k+1 := Fin.val_last (k+1)
  have hcs : (Fin.castSucc (Fin.last k) : Fin (k+2)).val = k := Fin.val_last k
  have h1 : (Fin.castSucc (Fin.last k) : Fin (k+2)) ≠ Fin.last (k+1) := by
    intro heq; have := congr_arg Fin.val heq; rw [hcs, hL] at this; omega
  rw [if_neg h1]
  have h2 : (Fin.castSucc (Fin.last k) : Fin (k+2)).val + 1 =
            (Fin.last (k+1) : Fin (k+2)).val := by rw [hcs, hL]
  rw [if_pos h2]
  congr 1
  exact hcs

lemma inner_last_col_zero (k : ℕ) (a b : ℕ → R) (i' : Fin (k+1)) (h : i' ≠ Fin.last k) :
    (charmatrix (tridiag (k+2) a b)) (Fin.castSucc i')
        ((Fin.castSucc (Fin.last k) : Fin (k+1)).succAbove (Fin.last k)) = 0 := by
  have hcol : (Fin.castSucc (Fin.last k) : Fin (k+1)).succAbove (Fin.last k) =
              Fin.last (k+1) := by
    rw [Fin.succAbove_castSucc_self]
    ext
    show (Fin.last k).succ.val = (Fin.last (k+1)).val
    simp [Fin.val_succ, Fin.val_last]
  rw [hcol, charmatrix_tridiag_apply]
  have hivc : (Fin.castSucc i' : Fin (k+2)).val = i'.val := rfl
  have hL : (Fin.last (k+1) : Fin (k+2)).val = k+1 := Fin.val_last (k+1)
  have hivallt : i'.val < k := by
    have hne : i'.val ≠ k := by
      intro heq; apply h; ext
      show i'.val = (Fin.last k).val
      rw [Fin.val_last]; exact heq
    have := i'.isLt; omega
  have h1 : (Fin.castSucc i' : Fin (k+2)) ≠ Fin.last (k+1) := by
    intro heq; have := congr_arg Fin.val heq; rw [hivc, hL] at this; omega
  rw [if_neg h1]
  rw [if_neg (by rw [hivc, hL]; omega), if_neg (by rw [hivc, hL]; omega)]

/-! ## Sign helpers -/

private lemma neg_one_pow_two_mul (m : ℕ) : ((-1 : R[X])) ^ (m + m) = 1 := by
  rw [← two_mul, pow_mul]; simp

private lemma neg_one_pow_two_mul_add_one (m : ℕ) :
    ((-1 : R[X])) ^ ((m + 1) + m) = -1 := by
  have h : (m + 1) + m = (m + m) + 1 := by ring
  rw [h, pow_succ, neg_one_pow_two_mul]; ring

/-! ## Main recurrence -/

theorem D_recurrence (a b : ℕ → R) (k : ℕ) :
    D a b (k + 2) =
      (X - C (a (k + 1))) * D a b (k + 1) - C (b k) ^ 2 * D a b k := by
  have hL_ne_CL : (Fin.last (k+1) : Fin (k+2)) ≠ Fin.castSucc (Fin.last k) := by
    intro heq
    have := congr_arg Fin.val heq
    rw [Fin.val_last (k+1)] at this
    rw [show (Fin.castSucc (Fin.last k) : Fin (k+2)).val = k from Fin.val_last k] at this
    omega
  show (charmatrix (tridiag (k+2) a b)).det = _
  rw [Matrix.det_succ_row _ (Fin.last (k+1))]
  rw [Fintype.sum_eq_add (β := R[X]) (Fin.last (k+1)) (Fin.castSucc (Fin.last k)) hL_ne_CL
      (by
        rintro j ⟨h1, h2⟩
        rw [last_row_zero k a b j h1 h2]
        ring)]
  have hL_succAbove :
      ((Fin.last (k+1) : Fin (k+2)).succAbove : Fin (k+1) → Fin (k+2)) = Fin.castSucc :=
    Fin.succAbove_last
  rw [hL_succAbove, charmatrix_submatrix_castSucc]
  rw [last_row_diag, last_row_subdiag]
  have hsign1 : ((-1 : R[X]))
      ^ ((Fin.last (k+1) : Fin (k+2)).val + (Fin.last (k+1) : Fin (k+2)).val) = 1 := by
    rw [Fin.val_last]; exact neg_one_pow_two_mul (k+1)
  have hsign2 : ((-1 : R[X]))
      ^ ((Fin.last (k+1) : Fin (k+2)).val + (Fin.castSucc (Fin.last k) : Fin (k+2)).val) = -1 := by
    rw [Fin.val_last]
    rw [show (Fin.castSucc (Fin.last k) : Fin (k+2)).val = k from Fin.val_last k]
    exact neg_one_pow_two_mul_add_one k
  rw [hsign1, hsign2]
  set M : Matrix (Fin (k+1)) (Fin (k+1)) R[X] :=
    (charmatrix (tridiag (k+2) a b)).submatrix
      (Fin.castSucc : Fin (k+1) → Fin (k+2))
      (Fin.castSucc (Fin.last k) : Fin (k+1)).succAbove with hM_def
  have hMdet : M.det = -C (b k) * D a b k := by
    rw [Matrix.det_succ_column M (Fin.last k)]
    rw [Fintype.sum_eq_single (Fin.last k)
        (by
          intro i' hi'
          show (-1) ^ _ * M i' (Fin.last k) * _ = 0
          have : M i' (Fin.last k) = 0 := by
            rw [hM_def]
            simp only [submatrix_apply]
            exact inner_last_col_zero k a b i' hi'
          rw [this]; ring)]
    have hMval : M (Fin.last k) (Fin.last k) = -C (b k) := by
      rw [hM_def]
      simp only [submatrix_apply]
      exact inner_last_col_at_last k a b
    have hL'_succAbove :
        ((Fin.last k : Fin (k+1)).succAbove : Fin k → Fin (k+1)) = Fin.castSucc :=
      Fin.succAbove_last
    have hsignM : ((-1 : R[X]))
        ^ ((Fin.last k : Fin (k+1)).val + (Fin.last k : Fin (k+1)).val) = 1 := by
      rw [Fin.val_last]; exact neg_one_pow_two_mul k
    have hMM_sub :
        (M.submatrix (Fin.last k).succAbove (Fin.last k).succAbove).det = D a b k := by
      rw [hL'_succAbove, hM_def]
      rw [show ((charmatrix (tridiag (k+2) a b)).submatrix
              (Fin.castSucc : Fin (k+1) → Fin (k+2))
              (Fin.castSucc (Fin.last k) : Fin (k+1)).succAbove).submatrix
              (Fin.castSucc : Fin k → Fin (k+1))
              (Fin.castSucc : Fin k → Fin (k+1))
            = charmatrix (tridiag k a b) from double_submatrix_eq k a b]
      rfl
    rw [hsignM, hMval, hMM_sub]
    ring
  rw [hMdet]
  show 1 * (X - C (a (k+1))) * D a b (k+1) + -1 * (-C (b k)) * (-C (b k) * D a b k) = _
  ring

theorem charpoly_tridiag_eq_D (a b : ℕ → R) (n : ℕ) :
    (tridiag n a b).charpoly = D a b n := rfl

end CausalAlgebraicGeometry.TridiagonalCharpoly
