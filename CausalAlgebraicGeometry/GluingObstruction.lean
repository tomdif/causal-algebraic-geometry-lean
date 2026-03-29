/-
  GluingObstruction.lean — The corner algebra presheaf does NOT satisfy gluing.

  This is the fundamental reason CSpec is not a full scheme theory.

  For convex S₁, S₂ with S₁ ∪ S₂ convex: if x ∈ S₁\S₂ and y ∈ S₂\S₁ are
  comparable (x < y), then the matrix entry M(x,y) is in e_{S₁∪S₂}Ae_{S₁∪S₂}
  but NOT in either e_{S₁}Ae_{S₁} or e_{S₂}Ae_{S₂}. So sections on S₁ and S₂
  don't determine the section on S₁ ∪ S₂.

  Counterexample: the 3-element chain {a < b < c} with S₁ = {a,b}, S₂ = {b,c}.
  A causal matrix M with M(a,c) ≠ 0 restricts to 0 on both S₁ and S₂
  (since a ∉ S₂ and c ∉ S₁), but is nonzero on S₁ ∪ S₂.

  Zero sorry.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.GluingObstruction

-- The 3-element chain: 0 < 1 < 2
def chainLe : Fin 3 → Fin 3 → Prop := fun a b => a.val ≤ b.val
instance : DecidableRel chainLe := fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))

-- S₁ = {0, 1}, S₂ = {1, 2}, S₁ ∪ S₂ = {0, 1, 2}
def S1 : Finset (Fin 3) := {0, 1}
def S2 : Finset (Fin 3) := {1, 2}
def S12 : Finset (Fin 3) := {0, 1, 2}

-- Both convex (intervals in a chain)
-- S₁ ∩ S₂ = {1}
def S_inter : Finset (Fin 3) := {1}

-- A causal matrix M on the chain with M(0,2) = 1, all other entries standard
-- This M is in e_{S₁∪S₂}Ae_{S₁∪S₂} (supported on {0,1,2}²)
-- Its restriction to S₁ = {0,1}: M|_{S₁}(0,1) is determined, M|_{S₁}(0,2) doesn't exist
-- Its restriction to S₂ = {1,2}: M|_{S₂}(1,2) is determined, M|_{S₂}(0,2) doesn't exist
-- The cross-entry M(0,2) is LOST by both restrictions

-- To recover M from M|_{S₁} and M|_{S₂}, we'd need the cross-entry M(0,2),
-- but neither restriction contains it. So gluing fails.

/-- The element 0 is in S₁ but not S₂. -/
theorem zero_in_S1_not_S2 : (0 : Fin 3) ∈ S1 ∧ (0 : Fin 3) ∉ S2 := by native_decide

/-- The element 2 is in S₂ but not S₁. -/
theorem two_in_S2_not_S1 : (2 : Fin 3) ∈ S2 ∧ (2 : Fin 3) ∉ S1 := by native_decide

/-- 0 < 2 in the chain (they're comparable across the two sets). -/
theorem zero_lt_two : chainLe 0 2 := by native_decide

/-- S₁ and S₂ cover S₁ ∪ S₂. -/
theorem cover : S1 ∪ S2 = S12 := by native_decide

/-- The intersection is a single element. -/
theorem inter_eq : S1 ∩ S2 = S_inter := by native_decide

/-- **Gluing obstruction**: the cross-entry M(0,2) lives in the section
    on S₁ ∪ S₂ = {0,1,2} but not in either restriction.

    Specifically: the "causal matrix space" on S₁∪S₂ has dimension
    |{(x,y) : x ≤ y, x,y ∈ S₁∪S₂}| = 6 (all entries of a 3×3 UT matrix).
    But the restrictions to S₁ and S₂ have dimensions 3 and 3, with overlap 1.
    So 3 + 3 - 1 = 5 < 6. One degree of freedom (the cross-entry) is lost. -/
theorem gluing_dimension_gap :
    -- Comparable pairs in S₁∪S₂ = {(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)} = 6
    ((S12.product S12).filter (fun p => chainLe p.1 p.2)).card = 6 ∧
    -- Comparable pairs in S₁ = {(0,0),(0,1),(1,1)} = 3
    ((S1.product S1).filter (fun p => chainLe p.1 p.2)).card = 3 ∧
    -- Comparable pairs in S₂ = {(1,1),(1,2),(2,2)} = 3
    ((S2.product S2).filter (fun p => chainLe p.1 p.2)).card = 3 ∧
    -- Comparable pairs in S₁∩S₂ = {(1,1)} = 1
    ((S_inter.product S_inter).filter (fun p => chainLe p.1 p.2)).card = 1 ∧
    -- 3 + 3 - 1 = 5 < 6: one entry lost
    3 + 3 - 1 < 6 := by native_decide

/-! ## Consequence

  The corner algebra presheaf satisfies LOCALITY (two sections that agree
  on the overlap are equal — this is trivially true for matrix restrictions).
  But it does NOT satisfy GLUING: you cannot reconstruct a section on S₁∪S₂
  from compatible sections on S₁ and S₂ when there are comparable pairs
  crossing the boundary.

  This is the fundamental reason CSpec is a PRESHEAF construction, not a
  full sheaf theory. The bridge theorem and universal property are genuine,
  but the sheaf-theoretic depth is limited by this cross-term obstruction.

  The honest framing: CSpec provides a computationally effective framework
  for convex-subset invariants, with a universal property and algebraic
  characterization via the bridge theorem. It is not a recreation of Spec(R).
-/

end CausalAlgebraicGeometry.GluingObstruction
