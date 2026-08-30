/-
  ChamberStructuralRoot.lean — Structural proof that
    chamberPoly d (topZero d) (d - 1) = 0   for all d ≥ 3.

  Strategy ("Geometric Collapse of the Causal Chamber Continued Fraction"):
    1. Boundary alignment:  b1sq d = Cint d * (topZero d - 1/3).
    2. Interior geometric formula: for 1 ≤ n ≤ d-2,
         chamberPoly d (topZero d) n = (topZero d - 1/3) * (xint d)^(n-1).
    3. Final step: blast_sq = (topZero d - 1/5) * xint d makes the last
       step collapse to 0.

  Then deduce that topZero d is a root of chamberPolynomial d, and that
  the deflation chamberPolynomial d = (X - C (topZero d)) * Q with
  Q.natDegree = d - 2 holds unconditionally for every d ≥ 3.
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import CausalAlgebraicGeometry.ChamberPolynomials
import CausalAlgebraicGeometry.ChamberDeflation

namespace CausalAlgebraicGeometry.ChamberPolynomials

open Polynomial

/-! ## Lemma 1 — boundary alignment -/

/-- Algebraic identity that lets the `n = 1 → 2` step look like an interior step. -/
lemma boundary_alignment (d : ℕ) (hd : 3 ≤ d) :
    b1sq d = Cint d * (topZero d - 1/3) := by
  unfold b1sq Cint topZero
  have hd1 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h1 : ((d : ℝ) + 1) ≠ 0 := by linarith
  have h2 : ((d : ℝ) - 2) ≠ 0 := by linarith
  field_simp
  ring

/-! ## Lemma 2 — geometric formula on the interior -/

/--
  Paired geometric formula. For `n + 1 ≤ d - 3`, both `D_{n+1}` and `D_{n+2}`
  satisfy the geometric form
    `D_k = (topZero d - 1/3) * (xint d)^(k-1)`.
  Pairing the statement lets a single induction step suffice.
-/
lemma chamberPoly_geometric_pair (d : ℕ) (hd : 4 ≤ d) :
    ∀ n, n + 1 ≤ d - 3 →
      chamberPoly d (topZero d) (n + 1) = (topZero d - 1/3) * (xint d) ^ n ∧
      chamberPoly d (topZero d) (n + 2) = (topZero d - 1/3) * (xint d) ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · -- D_1 = topZero d - 1/3
        simp [chamberPoly]
      · -- D_2: recurrence at index 0+2, with chamberDiag d 1 = 2/5,
        --   coupling = b1sq d, then Lemma 1 collapses everything.
        have hdiag : chamberDiag d 1 = 2/5 := by
          unfold chamberDiag
          have h2 : 2 < d - 1 := by omega
          simp [h2]
        show (topZero d - chamberDiag d 1) * (topZero d - 1/3)
              - (if (0 : ℕ) = 0 then b1sq d
                 else if (0 : ℕ) + 1 < d - 2 then bint_sq d
                 else blast_sq d) * 1
            = (topZero d - 1/3) * (xint d) ^ 1
        rw [hdiag]
        simp only [if_true]
        have hb : b1sq d = Cint d * (topZero d - 1/3) :=
          boundary_alignment d (by omega)
        rw [hb]
        simp only [xint, topZero, pow_succ, pow_zero, one_mul]
        ring
  | succ k ih =>
      intro hk
      have hk2 : k + 1 ≤ d - 3 := by omega
      obtain ⟨hA, hB⟩ := ih hk2
      refine ⟨hB, ?_⟩
      -- D_{k+3}: interior recurrence (chamberDiag d (k+2) = 2/5, coupling = bint_sq d).
      have hdiag : chamberDiag d (k + 2) = 2/5 := by
        unfold chamberDiag
        have h2 : (k + 2) + 1 < d - 1 := by omega
        simp [h2]
      have hcoup : (if (k + 1) = 0 then b1sq d
                    else if (k + 1) + 1 < d - 2 then bint_sq d
                    else blast_sq d) = bint_sq d := by
        have h2 : (k + 1) + 1 < d - 2 := by omega
        simp [h2]
      show (topZero d - chamberDiag d (k + 2)) * chamberPoly d (topZero d) (k + 2)
            - (if (k + 1) = 0 then b1sq d
               else if (k + 1) + 1 < d - 2 then bint_sq d
               else blast_sq d) * chamberPoly d (topZero d) (k + 1)
          = (topZero d - 1/3) * (xint d) ^ (k + 1 + 1)
      rw [hdiag, hcoup, hA, hB]
      simp only [bint_sq, xint, topZero, pow_succ]
      ring

/-- Geometric formula for `D_n` at `λ = topZero d`, valid on `1 ≤ n ≤ d - 2`. -/
lemma chamberPoly_geometric_interior (d : ℕ) (hd : 4 ≤ d)
    (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ d - 2) :
    chamberPoly d (topZero d) n = (topZero d - 1/3) * (xint d) ^ (n - 1) := by
  rcases Nat.lt_or_ge n (d - 2) with hlt | hge
  · -- n ≤ d - 3: first conjunct of the pair.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m + 1 ≤ d - 3 := by omega
    have h := (chamberPoly_geometric_pair d hd m hm).1
    simpa using h
  · -- n = d - 2: second conjunct, after writing d = k + 4.
    have hn_eq : n = d - 2 := by omega
    subst hn_eq
    obtain ⟨k, hk⟩ : ∃ k, d = k + 4 := ⟨d - 4, by omega⟩
    subst hk
    have h := (chamberPoly_geometric_pair (k + 4) hd k (by omega)).2
    -- Rewrite the deeper Nat-subtraction first to avoid masking it.
    have e2 : k + 4 - 2 - 1 = k + 1 := by omega
    have e1 : k + 4 - 2 = k + 2 := by omega
    rw [e2, e1]; exact h

/-! ## Main theorem -/

/-- The chamber polynomial vanishes at `topZero d` for every `d ≥ 3`. -/
theorem chamberPoly_topZero_zero (d : ℕ) (hd : 3 ≤ d) :
    chamberPoly d (topZero d) (d - 1) = 0 := by
  rcases eq_or_lt_of_le hd with rfl | hd4
  · -- d = 3: existing fact.
    exact topZero_is_zero_d3
  · -- d ≥ 4: combine the geometric formula at indices d-2, d-3 with
    -- the last-step recurrence (blast_sq = (topZero d - 1/5) * xint d).
    have hd4_ge : 4 ≤ d := hd4
    obtain ⟨m, hm⟩ : ∃ m, d = m + 4 := ⟨d - 4, by omega⟩
    subst hm
    have hdiag : chamberDiag (m + 4) (m + 2) = 1/5 := by
      unfold chamberDiag; simp
    have hcoup : (if (m + 1) = 0 then b1sq (m + 4)
                  else if (m + 1) + 1 < (m + 4) - 2 then bint_sq (m + 4)
                  else blast_sq (m + 4)) = blast_sq (m + 4) := by
      simp
    have hD2 : chamberPoly (m + 4) (topZero (m + 4)) (m + 2) =
        (topZero (m + 4) - 1/3) * (xint (m + 4)) ^ (m + 1) := by
      have h := chamberPoly_geometric_interior (m + 4) hd4_ge (m + 2)
                  (by omega) (by omega)
      have e : (m + 2 - 1) = (m + 1) := by omega
      rw [e] at h; exact h
    have hD1 : chamberPoly (m + 4) (topZero (m + 4)) (m + 1) =
        (topZero (m + 4) - 1/3) * (xint (m + 4)) ^ m := by
      have h := chamberPoly_geometric_interior (m + 4) hd4_ge (m + 1)
                  (by omega) (by omega)
      have e : (m + 1 - 1) = m := by omega
      rw [e] at h; exact h
    have hgoal : (m + 4 - 1) = (m + 3) := by omega
    rw [hgoal]
    show (topZero (m + 4) - chamberDiag (m + 4) (m + 2))
            * chamberPoly (m + 4) (topZero (m + 4)) (m + 2)
          - (if (m + 1) = 0 then b1sq (m + 4)
             else if (m + 1) + 1 < (m + 4) - 2 then bint_sq (m + 4)
             else blast_sq (m + 4))
            * chamberPoly (m + 4) (topZero (m + 4)) (m + 1) = 0
    rw [hdiag, hcoup, hD1, hD2]
    simp only [blast_sq, topZero, pow_succ]
    ring

/-! ## Polynomial deflation (corollary) -/

/-- `topZero d` is a root of `chamberPolynomial d` for every `d ≥ 3`. -/
theorem chamberPolynomial_topZero_isRoot (d : ℕ) (hd : 3 ≤ d) :
    (chamberPolynomial d).IsRoot (topZero d) := by
  show (chamberPolynomial d).eval (topZero d) = 0
  rw [eval_chamberPolynomial]
  exact chamberPoly_topZero_zero d hd

/-- Unconditional deflation: the chamber polynomial factors as
    `(X - C (topZero d)) * Q` with `Q.natDegree = d - 2`, for every `d ≥ 3`. -/
theorem chamber_deflation (d : ℕ) (hd : 3 ≤ d) :
    ∃ Q : Polynomial ℝ,
      chamberPolynomial d = (Polynomial.X - Polynomial.C (topZero d)) * Q ∧
      Q.natDegree = d - 2 :=
  chamber_deflation_of_root d (by omega)
    (topZero d) (chamberPolynomial_topZero_isRoot d hd)

end CausalAlgebraicGeometry.ChamberPolynomials
