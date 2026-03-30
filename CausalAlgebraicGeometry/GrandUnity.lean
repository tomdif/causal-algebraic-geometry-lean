/-
  GrandUnity.lean — Discrete concavity of S_BD for d = 2, 3, 4.

  PROVED: the BD action S_BD_d(m) is discretely concave for d = 2, 3, 4:
    f(n-1) + f(n+1) ≤ 2·f(n) for all n ≥ 1.

  The exact concavity defects:
    d=2: -2 (constant, degree 0)
    d=3: -12n + 6 (linear, degree 1)
    d=4: -36n² + 24n - 6 (quadratic, degree 2)

  The degree of the defect polynomial is d-2 — the same exponent that
  controls equilibrium entropy (m^{d-2}), temperature (m^{-(d-3)}),
  and Bekenstein marginality (m^{d-4}). This is not coincidence:
  it arises from the polynomial structure of the link-count formula.

  WHAT THIS SUPPORTS (not yet a single general-d theorem):
  Combined with the recursive decomposition (RecursiveBD.lean),
  the d=2 TV exactness (ExactBDFormula.lean), and the d=3
  TV-minimization benchmarks (NestedTVQuantitative.lean), these
  concavity identities support a conjectural recursive TV hierarchy
  across dimensions. The full all-d iterated-TV law remains a
  conjecture supported by these proved components.

  Zero sorry.
-/
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.GrandUnity

def sbd2 (m : ℤ) : ℤ := -(m - 1) ^ 2 + 1
def sbd3 (m : ℤ) : ℤ := -2 * m ^ 3 + 3 * m ^ 2
def sbd4 (m : ℤ) : ℤ := -3 * m ^ 4 + 4 * m ^ 3

theorem concavity_d2_exact (n : ℤ) :
    sbd2 (n - 1) + sbd2 (n + 1) - 2 * sbd2 n = -2 := by unfold sbd2; ring

theorem concavity_d2 (n : ℤ) :
    sbd2 (n - 1) + sbd2 (n + 1) ≤ 2 * sbd2 n := by linarith [concavity_d2_exact n]

theorem concavity_d3_exact (n : ℤ) :
    sbd3 (n - 1) + sbd3 (n + 1) - 2 * sbd3 n = -12 * n + 6 := by unfold sbd3; ring

theorem concavity_d3 (n : ℤ) (hn : 1 ≤ n) :
    sbd3 (n - 1) + sbd3 (n + 1) ≤ 2 * sbd3 n := by linarith [concavity_d3_exact n]

theorem concavity_d4_exact (n : ℤ) :
    sbd4 (n - 1) + sbd4 (n + 1) - 2 * sbd4 n = -36 * n ^ 2 + 24 * n - 6 := by unfold sbd4; ring

theorem concavity_d4 (n : ℤ) :
    sbd4 (n - 1) + sbd4 (n + 1) ≤ 2 * sbd4 n := by
  have h := concavity_d4_exact n; nlinarith [sq_nonneg (3 * n - 2)]

def sbd5 (m : ℤ) : ℤ := -4 * m ^ 5 + 5 * m ^ 4
def sbd6 (m : ℤ) : ℤ := -5 * m ^ 6 + 6 * m ^ 5

theorem concavity_d5_exact (n : ℤ) :
    sbd5 (n - 1) + sbd5 (n + 1) - 2 * sbd5 n =
    -80 * n ^ 3 + 60 * n ^ 2 - 40 * n + 10 := by unfold sbd5; ring

theorem concavity_d5 (n : ℤ) (hn : 1 ≤ n) :
    sbd5 (n - 1) + sbd5 (n + 1) ≤ 2 * sbd5 n := by
  have h := concavity_d5_exact n
  nlinarith [sq_nonneg (2 * n - 1), sq_nonneg n, sq_nonneg (n - 1)]

theorem concavity_d6_exact (n : ℤ) :
    sbd6 (n - 1) + sbd6 (n + 1) - 2 * sbd6 n =
    -150 * n ^ 4 + 120 * n ^ 3 - 150 * n ^ 2 + 60 * n - 10 := by unfold sbd6; ring

theorem concavity_d6 (n : ℤ) (hn : 1 ≤ n) :
    sbd6 (n - 1) + sbd6 (n + 1) ≤ 2 * sbd6 n := by
  have h := concavity_d6_exact n
  nlinarith [sq_nonneg n, sq_nonneg (n - 1), sq_nonneg (3 * n ^ 2 - n),
             sq_nonneg (n * (n - 1))]

theorem grand_unity (n : ℤ) (hn : 1 ≤ n) :
    (sbd2 (n-1) + sbd2 (n+1) ≤ 2 * sbd2 n) ∧
    (sbd3 (n-1) + sbd3 (n+1) ≤ 2 * sbd3 n) ∧
    (sbd4 (n-1) + sbd4 (n+1) ≤ 2 * sbd4 n) ∧
    (sbd5 (n-1) + sbd5 (n+1) ≤ 2 * sbd5 n) ∧
    (sbd6 (n-1) + sbd6 (n+1) ≤ 2 * sbd6 n) :=
  ⟨concavity_d2 n, concavity_d3 n hn, concavity_d4 n, concavity_d5 n hn, concavity_d6 n hn⟩

-- The degree of the concavity defect grows as d-2, matching the
-- thermodynamic exponent that controls equilibrium entropy scaling.
-- d=2: degree 0 (constant defect, topological gravity)
-- d=3: degree 1 (linear defect, onset of dynamical gravity)
-- d=4: degree 2 (quadratic defect, fully dynamical)
-- Conjecture: d=k gives degree k-2 defect for all k ≥ 2.

end CausalAlgebraicGeometry.GrandUnity
