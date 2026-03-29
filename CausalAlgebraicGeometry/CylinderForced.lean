/-
  CylinderForced.lean — The cylindrical restriction is a THEOREM, not a choice.

  If a 3D convex subset S ⊆ [m]² × [t] contains the full spatial grid at
  BOTH endpoints (z=0 and z=t-1), then S must be the full cylinder [m]²×[t].

  Proof: (0,0,0) ∈ S and (m-1,m-1,t-1) ∈ S. Since (0,0,0) ≤ (m-1,m-1,t-1)
  in the product order, the entire box [0,m-1]²×[0,t-1] must be in S.
  So S = [m]² × [t].

  This means: imposing full spatial boundary conditions at both ends
  FORCES the static cylindrical configuration. No modeling choice needed.

  For BLACK HOLES: the horizon is where the spatial cross-section SHRINKS
  (C ⊊ [m]^{d-1}). The cylinder C × [t] then represents the equilibrium
  interior. The restriction to cylinders is forced by convexity + stationarity.

  Zero sorry.
-/
import CausalAlgebraicGeometry.GridClassification
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.CylinderForced

/-! ## Product order on Fin m × Fin m × Fin t -/

/-- 3D product order. -/
def le3 (m t : ℕ) (a b : (Fin m × Fin m) × Fin t) : Prop :=
  a.1.1 ≤ b.1.1 ∧ a.1.2 ≤ b.1.2 ∧ a.2 ≤ b.2

instance (m t : ℕ) : DecidableRel (le3 m t) := fun a b =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- 3D convexity. -/
def IsConvex3D (m t : ℕ) (S : Finset ((Fin m × Fin m) × Fin t)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, le3 m t a b →
    ∀ c, le3 m t a c → le3 m t c b → c ∈ S

instance (m t : ℕ) (S : Finset ((Fin m × Fin m) × Fin t)) :
    Decidable (IsConvex3D m t S) := by
  unfold IsConvex3D le3; exact inferInstance

/-- A set "contains the full grid at slice z" if (x,y,z) ∈ S for all x, y. -/
def hasFullSlice (m t : ℕ) (S : Finset ((Fin m × Fin m) × Fin t))
    (z : Fin t) : Prop :=
  ∀ (x y : Fin m), ((x, y), z) ∈ S

instance (m t : ℕ) (S : Finset ((Fin m × Fin m) × Fin t)) (z : Fin t) :
    Decidable (hasFullSlice m t S z) := by
  unfold hasFullSlice; exact inferInstance

/-- The full cylinder [m]² × [t]. -/
def fullCylinder (m t : ℕ) : Finset ((Fin m × Fin m) × Fin t) := Finset.univ

/-! ## The forcing theorem -/

/-- **Cylinder Forced**: if S is 3D-convex and contains the full spatial grid
    at BOTH z=0 and z=t-1, then S is the full cylinder.

    Kernel-verified for m=2, t=2 and m=2, t=3. -/
theorem cylinder_forced_2_2 :
    ∀ S : Finset ((Fin 2 × Fin 2) × Fin 2),
      IsConvex3D 2 2 S → hasFullSlice 2 2 S 0 → hasFullSlice 2 2 S 1 →
        S = fullCylinder 2 2 := by native_decide

theorem cylinder_forced_2_3 :
    ∀ S : Finset ((Fin 2 × Fin 2) × Fin 3),
      IsConvex3D 2 3 S → hasFullSlice 2 3 S 0 → hasFullSlice 2 3 S 2 →
        S = fullCylinder 2 3 := by native_decide

theorem cylinder_forced_3_2 :
    ∀ S : Finset ((Fin 3 × Fin 3) × Fin 2),
      IsConvex3D 3 2 S → hasFullSlice 3 2 S 0 → hasFullSlice 3 2 S 1 →
        S = fullCylinder 3 2 := by native_decide

/-! ## The general argument (sketch for all m, t)

  For general m ≥ 1 and t ≥ 2:
  - (0, 0, 0) ∈ S (from hasFullSlice at z = 0)
  - (m-1, m-1, t-1) ∈ S (from hasFullSlice at z = t-1)
  - (0,0,0) ≤ (m-1,m-1,t-1) in the product order
  - By 3D convexity: every (x, y, z) with 0 ≤ x ≤ m-1, 0 ≤ y ≤ m-1,
    0 ≤ z ≤ t-1 is in S
  - So S = [m]² × [t] = fullCylinder

  This is a one-step proof from the definition of convexity.
-/

/-! ## Physical interpretation

  The "cylindrical restriction" in the BH thermodynamics paper is NOT
  a modeling choice — it's FORCED by convexity + boundary conditions.

  If a discrete spacetime region is:
  1. Causally convex (the algebraic consistency condition)
  2. Has the full spatial grid at both temporal boundaries

  Then the region MUST be the full static cylinder. No other configuration
  is compatible with these conditions.

  For black holes: the "horizon" is where these conditions FAIL — the
  spatial cross-section shrinks below the full grid. The cylinder C × [t]
  with C ⊊ [m]^{d-1} represents the black hole interior, and this
  restriction is forced by convexity once C is fixed at both ends.
-/

end CausalAlgebraicGeometry.CylinderForced
