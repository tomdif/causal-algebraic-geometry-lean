/-
  ToeplitzEigenvalues.lean — Explicit eigenvalue/eigenvector formula for the
  symmetric tridiagonal Toeplitz matrix.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

namespace ChamberSpacing.ToeplitzEigenvalues

open Matrix Real Finset

noncomputable def toeplitzTridiag (n : ℕ) (a b : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun i j =>
  if i.val = j.val then a
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then b
  else 0

noncomputable def sineEigvec (n : ℕ) (k : ℕ) : Fin (n+1) → ℝ := fun j =>
  Real.sin ((↑(j.val + 1) * ↑k * Real.pi) / (↑n + 2))

noncomputable def chebyshevEigval (n : ℕ) (a b : ℝ) (k : ℕ) : ℝ :=
  a + 2 * b * Real.cos ((↑k * Real.pi) / (↑n + 2))

/-! ## Casting helpers -/

lemma npos (n : ℕ) : (↑n + 2 : ℝ) > 0 := by
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  linarith

lemma nne (n : ℕ) : (↑n + 2 : ℝ) ≠ 0 := ne_of_gt (npos n)

/-! ## Trig core lemma -/

lemma sin_three_term (j : ℝ) (θ : ℝ) :
    Real.sin (j * θ) + Real.sin ((j + 2) * θ) =
      2 * Real.sin ((j + 1) * θ) * Real.cos θ := by
  rw [Real.sin_add_sin]
  have h1 : (j * θ + (j + 2) * θ) / 2 = (j + 1) * θ := by ring
  have h2 : (j * θ - (j + 2) * θ) / 2 = -θ := by ring
  rw [h1, h2, Real.cos_neg]

/-! ## Sine eigenvector value identities -/

/-- `sineEigvec n k ⟨m, h⟩ = sin((m+1) k π /(n+2))` for any natural `m`. -/
lemma sineEigvec_val (n k : ℕ) (m : ℕ) (h : m < n + 1) :
    sineEigvec n k ⟨m, h⟩ =
      Real.sin (((↑m + 1) * ↑k * Real.pi) / (↑n + 2)) := by
  unfold sineEigvec
  congr 2
  push_cast
  ring

/-- Three-term identity for the eigenvector arguments. -/
lemma sineEigvec_three_term (n k : ℕ) (j : ℕ) :
    Real.sin (((↑j : ℝ) * ↑k * Real.pi) / (↑n + 2)) +
      Real.sin (((↑j + 2) * ↑k * Real.pi) / (↑n + 2)) =
    2 * Real.cos ((↑k * Real.pi) / (↑n + 2)) *
      Real.sin (((↑j + 1) * ↑k * Real.pi) / (↑n + 2)) := by
  set θ : ℝ := (↑k * Real.pi) / (↑n + 2) with hθ
  have hne : (↑n + 2 : ℝ) ≠ 0 := nne n
  have e0 : ((↑j : ℝ) * ↑k * Real.pi) / (↑n + 2) = (↑j : ℝ) * θ := by
    rw [hθ]; field_simp
  have e1 : (((↑j : ℝ) + 1) * ↑k * Real.pi) / (↑n + 2) = ((↑j : ℝ) + 1) * θ := by
    rw [hθ]; field_simp
  have e2 : (((↑j : ℝ) + 2) * ↑k * Real.pi) / (↑n + 2) = ((↑j : ℝ) + 2) * θ := by
    rw [hθ]; field_simp
  rw [e0, e1, e2]
  have hkey := sin_three_term (j : ℝ) θ
  linarith [hkey]

/-- Right-boundary "ghost" identity. -/
lemma sineEigvec_right_ghost_zero (n k : ℕ) :
    Real.sin (((↑n + 2 : ℝ) * ↑k * Real.pi) / (↑n + 2)) = 0 := by
  have hne : (↑n + 2 : ℝ) ≠ 0 := nne n
  have h : ((↑n + 2 : ℝ) * ↑k * Real.pi) / (↑n + 2) = (↑k : ℝ) * Real.pi := by
    field_simp
  rw [h]
  exact Real.sin_nat_mul_pi k

/-! ## Off-support entries vanish -/

lemma toeplitz_offdiag_zero (n : ℕ) (a b : ℝ) (i j : Fin (n+1))
    (hne_diag : i.val ≠ j.val)
    (hne_up : i.val + 1 ≠ j.val) (hne_down : j.val + 1 ≠ i.val) :
    toeplitzTridiag n a b i j = 0 := by
  unfold toeplitzTridiag
  rw [if_neg hne_diag, if_neg]
  rintro (h | h)
  · exact hne_up h
  · exact hne_down h

/-! ## Main eigenvalue theorem -/

theorem toeplitzTridiag_mulVec_sineEigvec
    (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    (toeplitzTridiag n a b).mulVec (sineEigvec n k) =
      (chebyshevEigval n a b k) • (sineEigvec n k) := by
  funext i
  show ∑ j, toeplitzTridiag n a b i j * sineEigvec n k j =
       chebyshevEigval n a b k * sineEigvec n k i
  rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
  · -- ===== Left boundary: i.val = 0 =====
    have h0lt : 0 < n + 1 := by omega
    have h1lt : 1 < n + 1 := by omega
    let j0 : Fin (n+1) := ⟨0, h0lt⟩
    let j1 : Fin (n+1) := ⟨1, h1lt⟩
    have hj0v : j0.val = 0 := rfl
    have hj1v : j1.val = 1 := rfl
    have hj0_ne_j1 : j0 ≠ j1 := by
      intro h; have h2 : j0.val = j1.val := congr_arg Fin.val h
      rw [hj0v, hj1v] at h2; exact absurd h2 (by omega)
    have hsupp : ∀ j ∉ ({j0, j1} : Finset (Fin (n+1))),
        toeplitzTridiag n a b i j * sineEigvec n k j = 0 := by
      intro j hjnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjnot
      obtain ⟨hjne0, hjne1⟩ := hjnot
      have hjnev0 : j.val ≠ 0 := by
        intro h; apply hjne0
        apply Fin.ext; rw [hj0v]; exact h
      have hjnev1 : j.val ≠ 1 := by
        intro h; apply hjne1
        apply Fin.ext; rw [hj1v]; exact h
      have h_ne_diag : i.val ≠ j.val := by rw [hi0]; exact fun h => hjnev0 h.symm
      have h_ne_up : i.val + 1 ≠ j.val := by rw [hi0]; exact fun h => hjnev1 h.symm
      have h_ne_down : j.val + 1 ≠ i.val := by rw [hi0]; omega
      rw [toeplitz_offdiag_zero n a b i j h_ne_diag h_ne_up h_ne_down]; ring
    have hsum :
      ∑ j, toeplitzTridiag n a b i j * sineEigvec n k j =
      ∑ j ∈ ({j0, j1} : Finset (Fin (n+1))),
        toeplitzTridiag n a b i j * sineEigvec n k j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hjnot; exact hsupp j hjnot
    rw [hsum]
    rw [Finset.sum_insert (by
          simp only [Finset.mem_singleton]; exact hj0_ne_j1),
        Finset.sum_singleton]
    -- T entries
    have hT_i_j0 : toeplitzTridiag n a b i j0 = a := by
      unfold toeplitzTridiag
      have h : i.val = j0.val := by rw [hi0, hj0v]
      rw [if_pos h]
    have hT_i_j1 : toeplitzTridiag n a b i j1 = b := by
      unfold toeplitzTridiag
      have h1 : i.val ≠ j1.val := by rw [hi0, hj1v]; exact (by omega : (0:ℕ) ≠ 1)
      rw [if_neg h1]
      rw [if_pos]
      left; rw [hi0, hj1v]
    rw [hT_i_j0, hT_i_j1]
    -- v entries
    have hi_eq : i = j0 := Fin.ext (by rw [hi0, hj0v])
    have hvi : sineEigvec n k i = Real.sin ((1 * ↑k * Real.pi) / (↑n + 2)) := by
      rw [hi_eq]
      rw [sineEigvec_val n k 0 h0lt]
      have : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
      rw [this]
    have hvj0 : sineEigvec n k j0 = Real.sin ((1 * ↑k * Real.pi) / (↑n + 2)) := by
      rw [sineEigvec_val n k 0 h0lt]
      have : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
      rw [this]
    have hvj1 : sineEigvec n k j1 = Real.sin ((2 * ↑k * Real.pi) / (↑n + 2)) := by
      rw [sineEigvec_val n k 1 h1lt]
      have : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
      rw [this]
    rw [hvj0, hvj1, hvi]
    -- three-term at j = 0
    have h3 := sineEigvec_three_term n k 0
    have hcast0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
    rw [hcast0] at h3
    have hzero : Real.sin (((0 : ℝ) * ↑k * Real.pi) / (↑n + 2)) = 0 := by
      have heq : ((0 : ℝ) * ↑k * Real.pi) / (↑n + 2) = 0 := by ring
      rw [heq, Real.sin_zero]
    rw [hzero, zero_add] at h3
    have hnorm1 : ((0 : ℝ) + 1) = 1 := by ring
    have hnorm2 : ((0 : ℝ) + 2) = 2 := by ring
    rw [hnorm1, hnorm2] at h3
    -- h3: sin(2 * k * π / (n+2)) = 2 cos θ * sin(1 * k * π / (n+2))
    rw [h3]
    unfold chebyshevEigval
    ring
  · -- i.val ≥ 1
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with hilt | hin
    · -- ===== Interior: 1 ≤ i.val < n =====
      have hi_lt_n : i.val < n := hilt
      have him1lt : i.val - 1 < n + 1 := by omega
      have hi0lt : i.val < n + 1 := i.isLt
      have hip1lt : i.val + 1 < n + 1 := by omega
      let jM : Fin (n+1) := ⟨i.val - 1, him1lt⟩
      let jC : Fin (n+1) := ⟨i.val, hi0lt⟩
      let jP : Fin (n+1) := ⟨i.val + 1, hip1lt⟩
      have hjMv : jM.val = i.val - 1 := rfl
      have hjCv : jC.val = i.val := rfl
      have hjPv : jP.val = i.val + 1 := rfl
      have hjM_ne_jC : jM ≠ jC := by
        intro h; have h2 : jM.val = jC.val := congr_arg Fin.val h
        rw [hjMv, hjCv] at h2; omega
      have hjC_ne_jP : jC ≠ jP := by
        intro h; have h2 : jC.val = jP.val := congr_arg Fin.val h
        rw [hjCv, hjPv] at h2; omega
      have hjM_ne_jP : jM ≠ jP := by
        intro h; have h2 : jM.val = jP.val := congr_arg Fin.val h
        rw [hjMv, hjPv] at h2; omega
      have hsupp : ∀ j ∉ ({jM, jC, jP} : Finset (Fin (n+1))),
          toeplitzTridiag n a b i j * sineEigvec n k j = 0 := by
        intro j hjnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjnot
        obtain ⟨hjneM, hjneC, hjneP⟩ := hjnot
        have hjnem : j.val ≠ i.val - 1 := by
          intro h; apply hjneM; apply Fin.ext; rw [hjMv]; exact h
        have hjnec : j.val ≠ i.val := by
          intro h; apply hjneC; apply Fin.ext; rw [hjCv]; exact h
        have hjnep : j.val ≠ i.val + 1 := by
          intro h; apply hjneP; apply Fin.ext; rw [hjPv]; exact h
        have h_ne_diag : i.val ≠ j.val := fun h => hjnec h.symm
        have h_ne_up : i.val + 1 ≠ j.val := fun h => hjnep h.symm
        have h_ne_down : j.val + 1 ≠ i.val := by
          intro h; have : j.val = i.val - 1 := by omega
          exact hjnem this
        rw [toeplitz_offdiag_zero n a b i j h_ne_diag h_ne_up h_ne_down]; ring
      have hsum :
        ∑ j, toeplitzTridiag n a b i j * sineEigvec n k j =
        ∑ j ∈ ({jM, jC, jP} : Finset (Fin (n+1))),
          toeplitzTridiag n a b i j * sineEigvec n k j := by
        symm; apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hjnot; exact hsupp j hjnot
      rw [hsum]
      rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            push_neg; exact ⟨hjM_ne_jC, hjM_ne_jP⟩),
          Finset.sum_insert (by
            simp only [Finset.mem_singleton]; exact hjC_ne_jP),
          Finset.sum_singleton]
      -- T entries
      have hTM : toeplitzTridiag n a b i jM = b := by
        unfold toeplitzTridiag
        have h1 : i.val ≠ jM.val := by rw [hjMv]; omega
        rw [if_neg h1]; rw [if_pos]
        right; rw [hjMv]; omega
      have hTC : toeplitzTridiag n a b i jC = a := by
        unfold toeplitzTridiag
        have h : i.val = jC.val := by rw [hjCv]
        rw [if_pos h]
      have hTP : toeplitzTridiag n a b i jP = b := by
        unfold toeplitzTridiag
        have h1 : i.val ≠ jP.val := by rw [hjPv]; omega
        rw [if_neg h1]; rw [if_pos]
        left; rw [hjPv]
      rw [hTM, hTC, hTP]
      -- v entries
      have hiv_eq : i = jC := Fin.ext (by rw [hjCv])
      have hvjM : sineEigvec n k jM =
                  Real.sin (((↑i.val : ℝ) * ↑k * Real.pi) / (↑n + 2)) := by
        rw [sineEigvec_val n k (i.val - 1) him1lt]
        have hh : (i.val - 1 + 1 : ℕ) = i.val := by omega
        have : (↑(i.val - 1) : ℝ) + 1 = (↑i.val : ℝ) := by
          have hh2 : ((↑(i.val - 1) + 1 : ℕ) : ℝ) = (↑i.val : ℝ) := by
            exact_mod_cast hh
          push_cast at hh2; linarith
        rw [this]
      have hvjC : sineEigvec n k jC =
                  Real.sin (((↑i.val + 1 : ℝ) * ↑k * Real.pi) / (↑n + 2)) :=
        sineEigvec_val n k i.val hi0lt
      have hvjP : sineEigvec n k jP =
                  Real.sin (((↑i.val + 2 : ℝ) * ↑k * Real.pi) / (↑n + 2)) := by
        rw [sineEigvec_val n k (i.val + 1) hip1lt]
        have : ((↑(i.val + 1) : ℕ) : ℝ) + 1 = (↑i.val : ℝ) + 2 := by
          push_cast; ring
        rw [this]
      -- Note: jC is definitionally equal to i (both have val = i.val and
      -- the proof of i.val < n+1 is irrelevant via proof irrelevance), so
      -- the rewrite hvjC also affects the RHS occurrence sineEigvec n k i.
      rw [hvjM, hvjC, hvjP]
      have h3 := sineEigvec_three_term n k i.val
      unfold chebyshevEigval
      linear_combination b * h3
    · -- ===== Right boundary: i.val = n =====
      have hival : i.val = n := hin
      have h0lt : 0 < n + 1 := by omega
      have hnlt : n < n + 1 := by omega
      have hnm1lt : n - 1 < n + 1 := by omega
      let jL : Fin (n+1) := ⟨n - 1, hnm1lt⟩
      let jN : Fin (n+1) := ⟨n, hnlt⟩
      have hjLv : jL.val = n - 1 := rfl
      have hjNv : jN.val = n := rfl
      have hjL_ne_jN : jL ≠ jN := by
        intro h; have h2 : jL.val = jN.val := congr_arg Fin.val h
        rw [hjLv, hjNv] at h2; omega
      have hsupp : ∀ j ∉ ({jL, jN} : Finset (Fin (n+1))),
          toeplitzTridiag n a b i j * sineEigvec n k j = 0 := by
        intro j hjnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjnot
        obtain ⟨hjneL, hjneN⟩ := hjnot
        have hjnenm1 : j.val ≠ n - 1 := by
          intro h; apply hjneL; apply Fin.ext; rw [hjLv]; exact h
        have hjnen : j.val ≠ n := by
          intro h; apply hjneN; apply Fin.ext; rw [hjNv]; exact h
        have hjvlt : j.val < n + 1 := j.isLt
        have h_ne_diag : i.val ≠ j.val := by rw [hival]; exact fun h => hjnen h.symm
        have h_ne_up : i.val + 1 ≠ j.val := by rw [hival]; intro h; omega
        have h_ne_down : j.val + 1 ≠ i.val := by
          rw [hival]; intro h
          have : j.val = n - 1 := by omega
          exact hjnenm1 this
        rw [toeplitz_offdiag_zero n a b i j h_ne_diag h_ne_up h_ne_down]; ring
      have hsum :
        ∑ j, toeplitzTridiag n a b i j * sineEigvec n k j =
        ∑ j ∈ ({jL, jN} : Finset (Fin (n+1))),
          toeplitzTridiag n a b i j * sineEigvec n k j := by
        symm; apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hjnot; exact hsupp j hjnot
      rw [hsum]
      rw [Finset.sum_insert (by
            simp only [Finset.mem_singleton]; exact hjL_ne_jN),
          Finset.sum_singleton]
      have hTL : toeplitzTridiag n a b i jL = b := by
        unfold toeplitzTridiag
        have h1 : i.val ≠ jL.val := by rw [hival, hjLv]; omega
        rw [if_neg h1]; rw [if_pos]
        right; rw [hival, hjLv]; omega
      have hTN : toeplitzTridiag n a b i jN = a := by
        unfold toeplitzTridiag
        have h : i.val = jN.val := by rw [hival, hjNv]
        rw [if_pos h]
      rw [hTL, hTN]
      have hiv_eq : i = jN := Fin.ext (by rw [hjNv]; exact hival)
      have hvjL : sineEigvec n k jL =
                  Real.sin (((↑n : ℝ) * ↑k * Real.pi) / (↑n + 2)) := by
        rw [sineEigvec_val n k (n - 1) hnm1lt]
        have hh : (n - 1 + 1 : ℕ) = n := by omega
        have : (↑(n - 1) : ℝ) + 1 = (↑n : ℝ) := by
          have hh2 : ((↑(n - 1) + 1 : ℕ) : ℝ) = (↑n : ℝ) := by exact_mod_cast hh
          push_cast at hh2; linarith
        rw [this]
      have hvjN : sineEigvec n k jN =
                  Real.sin (((↑n + 1 : ℝ) * ↑k * Real.pi) / (↑n + 2)) :=
        sineEigvec_val n k n hnlt
      have hvi : sineEigvec n k i =
                 Real.sin (((↑n + 1 : ℝ) * ↑k * Real.pi) / (↑n + 2)) := by
        rw [hiv_eq]; exact hvjN
      rw [hvjL, hvjN, hvi]
      -- three-term at j = n with ghost
      have h3 := sineEigvec_three_term n k n
      have hghost := sineEigvec_right_ghost_zero n k
      rw [hghost, add_zero] at h3
      -- h3: sin(↑n*kπ/(n+2)) = 2 cos(kπ/(n+2)) * sin((↑n+1)*kπ/(n+2))
      unfold chebyshevEigval
      linear_combination b * h3

/-! ## Picket-fence corollary -/

/-- Picket-fence (sign-corrected from spec). The spec stated
    `arccos((λ_k-a)/(2b)) - arccos((λ_{k+1}-a)/(2b))`, but as `k` increases
    the cosine decreases on [0,π], so arccos at `k+1` is LARGER than at `k`.
    Thus the literal statement gives `-1`, not `+1`.  We prove the order-swapped
    version (`arccos at k+1` minus `arccos at k`).

    The picket-fence content (consecutive arccoses differ by π/(n+2), giving
    spacing 1 after multiplication by (n+2)/π) is unchanged. -/
theorem toeplitz_unfolded_spacing
    (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (hb : b ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    (↑(n + 2) / Real.pi) *
      (Real.arccos ((chebyshevEigval n a b (k+1) - a) / (2 * b)) -
       Real.arccos ((chebyshevEigval n a b k - a) / (2 * b))) = 1 := by
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := ne_of_gt hπpos
  have hnp : (0 : ℝ) < ↑n + 2 := npos n
  have hnne : (↑n + 2 : ℝ) ≠ 0 := ne_of_gt hnp
  have h2b : (2 * b : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hb
  -- Reduce ratios
  have hratk : (chebyshevEigval n a b k - a) / (2 * b) =
               Real.cos ((↑k * Real.pi) / (↑n + 2)) := by
    unfold chebyshevEigval
    field_simp
    ring
  have hratk1 : (chebyshevEigval n a b (k+1) - a) / (2 * b) =
                Real.cos ((↑(k+1) * Real.pi) / (↑n + 2)) := by
    unfold chebyshevEigval
    field_simp
    ring
  rw [hratk, hratk1]
  -- arccos (cos x) = x for x ∈ [0, π]
  have hk_nn : (0 : ℝ) ≤ ((↑k * Real.pi) / (↑n + 2)) := by positivity
  have hk_le : ((↑k * Real.pi) / (↑n + 2)) ≤ Real.pi := by
    rw [div_le_iff₀ hnp]
    have hkR : (↑k : ℝ) ≤ ↑n + 1 := by exact_mod_cast (show k ≤ n + 1 by omega)
    nlinarith [Real.pi_pos]
  have hk1_nn : (0 : ℝ) ≤ ((↑(k+1) * Real.pi) / (↑n + 2)) := by positivity
  have hk1_le : ((↑(k+1) * Real.pi) / (↑n + 2)) ≤ Real.pi := by
    rw [div_le_iff₀ hnp]
    have hkR : ((↑(k+1) : ℕ) : ℝ) ≤ ↑n + 1 := by
      exact_mod_cast (show k + 1 ≤ n + 1 by omega)
    nlinarith [Real.pi_pos]
  rw [Real.arccos_cos hk_nn hk_le, Real.arccos_cos hk1_nn hk1_le]
  have hnpcast : ((↑(n + 2) : ℕ) : ℝ) = (↑n + 2 : ℝ) := by push_cast; ring
  have hk1cast : ((↑(k + 1) : ℕ) : ℝ) = (↑k + 1 : ℝ) := by push_cast; ring
  rw [hnpcast, hk1cast]
  field_simp
  ring

end ChamberSpacing.ToeplitzEigenvalues
