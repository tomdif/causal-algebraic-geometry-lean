/-
  ChiralNoGo.lean — The open-boundary chiral no-go theorem

  THEOREM: On a lattice with open boundary conditions, the gauged
  Möbius operator μ₁^g = I - g·S is upper triangular with 1's on
  the diagonal. Therefore det(μ₁^g) = 1 for ALL gauge configurations.
  The chiral determinant is trivial: the open-boundary chamber theory
  is inevitably vectorlike.

  This settles the chirality question: nontrivial chiral dynamics
  requires topological compactification (periodic BC), where
  det(μ₁^g) = 1 - W depends on the Wilson loop W = Π g_i.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring

namespace CausalAlgebraicGeometry.ChiralNoGo

open Matrix

/-! ### Section 1: The open-boundary shift operator -/

/-- The forward shift operator on Fin m (open boundary):
    S(i,j) = 1 if j = i + 1, else 0.
    This is STRICTLY upper triangular: S(i,j) = 0 for j ≤ i. -/
noncomputable def shiftMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => if j.val = i.val + 1 then 1 else 0

/-- The shift matrix is strictly upper triangular: zero on and below diagonal. -/
theorem shift_upper_triangular (m : ℕ) (i j : Fin m) (h : j.val ≤ i.val) :
    shiftMatrix m i j = 0 := by
  simp only [shiftMatrix, Matrix.of_apply]
  split
  · rename_i h'; omega
  · rfl

/-- The shift matrix has zero diagonal. -/
theorem shift_diag_zero (m : ℕ) (i : Fin m) : shiftMatrix m i i = 0 := by
  exact shift_upper_triangular m i i (le_refl _)

/-! ### Section 2: The gauged Möbius operator -/

/-- The gauged Möbius operator: μ₁^g(i,j) = δ(i,j) - g(i) · S(i,j)
    where g : Fin m → ℤ is the gauge field on links.
    For simplicity we work over ℤ; the result holds over any commutative ring. -/
noncomputable def gaugedMu (m : ℕ) (g : Fin m → ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - g i * shiftMatrix m i j

/-- The gauged Möbius operator is upper triangular with 1's on the diagonal.
    Proof: for j ≤ i, the shift term is 0 (shift is strictly upper triangular),
    so gaugedMu(i,j) = δ(i,j). In particular, diagonal entries are 1. -/
theorem gaugedMu_upper_triangular (m : ℕ) (g : Fin m → ℤ) (i j : Fin m)
    (h : j.val < i.val) : gaugedMu m g i j = 0 := by
  simp only [gaugedMu, Matrix.of_apply]
  rw [shift_upper_triangular m i j (le_of_lt h)]
  simp [Fin.ne_of_gt h]

theorem gaugedMu_diag (m : ℕ) (g : Fin m → ℤ) (i : Fin m) :
    gaugedMu m g i i = 1 := by
  simp only [gaugedMu, Matrix.of_apply, shift_diag_zero, mul_zero, sub_zero, if_true]

/-! ### Section 3: The no-go theorem -/

/-- **THE NO-GO THEOREM**: On a lattice with open boundary conditions,
    the gauged chiral determinant is identically 1 for all gauge fields.

    det(I - g·S) = 1

    Proof: I - g·S is upper triangular with 1's on the diagonal,
    so its determinant is the product of diagonal entries = 1^m = 1.

    Consequence: the chiral sector of the open-boundary chamber theory
    carries no gauge dynamics. The theory is inevitably vectorlike.
    Nontrivial chirality requires topological compactification (periodic BC). -/
theorem gaugedMu_blockTriangular (m : ℕ) (g : Fin m → ℤ) :
    (gaugedMu m g).BlockTriangular id := by
  intro i j hij
  -- hij : id j < id i, i.e., j < i
  exact gaugedMu_upper_triangular m g i j hij

theorem chiral_nogo (m : ℕ) (g : Fin m → ℤ) :
    (gaugedMu m g).det = 1 := by
  rw [Matrix.det_of_upperTriangular (gaugedMu_blockTriangular m g)]
  simp [gaugedMu_diag]

/-! ### Section 4: The periodic escape -/

/-- On a PERIODIC lattice (circle), the shift wraps: S(m-1, 0) = 1.
    The gauged determinant becomes det(I - g·S_per) = 1 - W
    where W = g₀ · g₁ · ... · g_{m-1} is the Wilson loop.
    This is NONTRIVIAL when W ≠ 1.

    We state this as a definition; the proof that det = 1 - W
    is a standard computation (expansion of the determinant of
    a companion-like matrix). -/
noncomputable def periodicShift (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j =>
    if j.val = (i.val + 1) % m then 1 else 0

noncomputable def wilsonLoop (m : ℕ) (g : Fin m → ℤ) : ℤ :=
  ∏ i : Fin m, g i

/-! ### Summary

**Open boundary (PROVED):**
  det(I - g·S) = 1 for all g.
  The chiral sector is trivial.
  The theory is inevitably vectorlike.

**Periodic boundary (STATED):**
  det(I - g·S_per) = 1 - W where W = Π g_i.
  The chiral sector depends on holonomy.
  Chirality enters through topology.

The no-go theorem `chiral_nogo` is the decisive result:
  it proves that the bare open-boundary chamber theory
  cannot produce nontrivial chiral gauge dynamics.
  Chirality, if it exists in this framework, must enter
  through topological compactification (periodic BC).
-/

end CausalAlgebraicGeometry.ChiralNoGo
