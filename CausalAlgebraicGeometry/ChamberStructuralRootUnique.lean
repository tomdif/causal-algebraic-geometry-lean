/-
  ChamberStructuralRootUnique.lean — Uniqueness / characterization layer
  for the geometric-collapse forced root.

  The existence theorem `chamberPoly_topZero_zero` was proved in
  `ChamberStructuralRoot.lean` via the chain
        boundary_alignment + interior geometric collapse + final cancellation.
  Each link in that chain is itself a one-equation-in-λ algebraic identity;
  we now show that *each* of those identities is satisfied by a unique
  real value of λ, namely `topZero d`.

  Headline:
    > λ* = (d-1)/(d+1) is uniquely characterized as the value at which
    > the chamber Feshbach continued fraction collapses geometrically.

  Three uniqueness theorems:

    1. `topZero_unique_from_b1sq`:
         b1sq d = Cint d * (λ - 1/3)  ↔  λ = topZero d
       (the FIRST-step geometric condition forces λ = topZero d).

    2. `topZero_unique_from_blast`:
         blast_sq d = (λ - 1/5) * xint d  ↔  λ = topZero d
       (the LAST-step terminal cancellation condition independently
        forces λ = topZero d).

    3. `topZero_geometric_collapse_characterization`:
         The two boundary identities are simultaneously satisfied by λ
         iff λ = topZero d.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import CausalAlgebraicGeometry.ChamberPolynomials
import CausalAlgebraicGeometry.ChamberStructuralRoot

namespace CausalAlgebraicGeometry.ChamberPolynomials

/-! ## Nonvanishing of `Cint` and `xint` -/

lemma Cint_ne_zero (d : ℕ) (hd : 3 ≤ d) : Cint d ≠ 0 := by
  have hpos := Cint_pos d hd
  exact ne_of_gt hpos

lemma xint_three : xint 3 = -1/5 := by
  unfold xint Cint
  push_cast
  norm_num

lemma xint_ne_zero (d : ℕ) (hd : 3 ≤ d) : xint d ≠ 0 := by
  rcases eq_or_lt_of_le hd with rfl | hd4
  · rw [xint_three]; norm_num
  · exact (xint_pos d hd4).ne'

/-! ## Uniqueness from the first-step (boundary) identity -/

/-- The first-step geometric condition `b1sq d = Cint d · (λ − 1/3)` has the
    unique solution `λ = topZero d`.  Equivalently, the boundary alignment
    identity is the *defining* equation of the structural root. -/
theorem topZero_unique_from_b1sq (d : ℕ) (hd : 3 ≤ d) (lam : ℝ) :
    b1sq d = Cint d * (lam - 1/3) ↔ lam = topZero d := by
  constructor
  · intro h
    have h_top := boundary_alignment d hd
    -- both equal `b1sq d`, so equal to each other
    have heq : Cint d * (lam - 1/3) = Cint d * (topZero d - 1/3) := by
      rw [← h, ← h_top]
    have hcancel : lam - 1/3 = topZero d - 1/3 :=
      mul_left_cancel₀ (Cint_ne_zero d hd) heq
    linarith
  · rintro rfl
    exact boundary_alignment d hd

/-! ## Uniqueness from the last-step (terminal) identity -/

/-- The last-step terminal cancellation `blast_sq d = (λ − 1/5) · xint d` has
    the unique solution `λ = topZero d`.  This is the second independent
    one-equation characterization of the structural root. -/
theorem topZero_unique_from_blast (d : ℕ) (hd : 3 ≤ d) (lam : ℝ) :
    blast_sq d = (lam - 1/5) * xint d ↔ lam = topZero d := by
  constructor
  · intro h
    -- by definition, blast_sq d = (topZero d - 1/5) * xint d
    have h_top : blast_sq d = (topZero d - 1/5) * xint d := by
      unfold blast_sq topZero; rfl
    rw [h_top] at h
    -- (topZero d - 1/5) * xint d = (lam - 1/5) * xint d
    have hcancel : topZero d - 1/5 = lam - 1/5 :=
      mul_right_cancel₀ (xint_ne_zero d hd) h
    linarith
  · rintro rfl
    unfold blast_sq topZero; rfl

/-! ## Joint characterization: geometric collapse ⇔ λ = topZero -/

/-- **Geometric-collapse characterization.**
    A real `λ` simultaneously satisfies the first-step and last-step boundary
    identities iff `λ = topZero d`.

    This is the cleanest statement of the "geometric collapse" mechanism:
    the structural eigenvalue is uniquely the value at which both ends of the
    continued fraction align — the first step becomes geometric and the last
    step terminates. -/
theorem topZero_geometric_collapse_characterization
    (d : ℕ) (hd : 3 ≤ d) (lam : ℝ) :
    (b1sq d = Cint d * (lam - 1/3) ∧ blast_sq d = (lam - 1/5) * xint d)
      ↔ lam = topZero d := by
  refine ⟨fun ⟨h1, _⟩ => ?_, fun hlam => ?_⟩
  · exact (topZero_unique_from_b1sq d hd lam).mp h1
  · subst hlam
    exact ⟨boundary_alignment d hd, (topZero_unique_from_blast d hd _).mpr rfl⟩

/-! ## Compatibility of the two boundary identities

    The two one-equation characterizations would in principle be inconsistent
    if they pinned down different values of λ. We make their consistency
    explicit: at `λ = topZero d`, both identities hold. -/

/-- Both boundary identities hold simultaneously at `λ = topZero d`. -/
theorem topZero_satisfies_both_boundary_identities (d : ℕ) (hd : 3 ≤ d) :
    b1sq d = Cint d * (topZero d - 1/3) ∧
    blast_sq d = (topZero d - 1/5) * xint d := by
  refine ⟨boundary_alignment d hd, ?_⟩
  unfold blast_sq topZero; rfl

end CausalAlgebraicGeometry.ChamberPolynomials
