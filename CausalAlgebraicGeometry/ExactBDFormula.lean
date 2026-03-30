/-
  ExactBDFormula.lean — The EXACT BD action on variable-width grids.

  THEOREM: For a variable-width grid with T rows and widths w₀,...,w_{T-1}:

    S_BD = T - n + (w₀ + w_{T-1} + TV) / 2

  where n = Σw_i is the total element count and TV = Σ|w_{i+1} - w_i| is
  the total variation of the width profile.

  PROOF: S_BD = |S| - hLinks - vLinks.
    |S| = n = Σw_i.
    hLinks = Σ(w_i - 1) = n - T.
    vLinks = Σmin(w_i, w_{i+1}).
    min(a,b) = (a + b - |a - b|) / 2.
    So vLinks = (Σ(w_i + w_{i+1}) - TV) / 2 = (2n - w₀ - w_{T-1} - TV) / 2.
    S_BD = n - (n-T) - (2n - w₀ - w_{T-1} - TV)/2
         = T - (2n - w₀ - w_{T-1} - TV)/2
         = T - n + (w₀ + w_{T-1} + TV)/2.

  CONSEQUENCE: The BD action is NOT the discrete Einstein-Hilbert action.
  It is a TOTAL VARIATION functional. The JT gravity correlation
  (R² ≈ 0.75 between S_BD and R + LogSch) arises because the discrete
  curvature R and log-Schwarzian approximate the total variation,
  but the exact functional is TV + boundary terms.

  This is a stronger result than the JT regression: it gives the
  EXACT decomposition of S_BD, not an approximate fit.

  Zero sorry.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace CausalAlgebraicGeometry.ExactBDFormula

/-! ## The min identity -/

/-- min(a,b) + max(a,b) = a + b. -/
theorem min_add_max (a b : ℕ) : min a b + max a b = a + b := by omega

/-- 2 * min(a,b) = a + b - |a - b| (in ℕ with dist). -/
theorem two_min_eq (a b : ℕ) : 2 * min a b = a + b - (max a b - min a b) := by omega

/-! ## S_BD decomposition for variable-width grids -/

-- The exact formula is proved computationally for specific profiles:
-- S_BD = T - n + (w₀ + w_{T-1} + TV) / 2

/-- For a 3-row grid with widths (a, b, c): n = a+b+c, T = 3.
    hLinks = (a-1) + (b-1) + (c-1) = n - 3.
    vLinks = min(a,b) + min(b,c).
    S_BD = n - (n-3) - min(a,b) - min(b,c) = 3 - min(a,b) - min(b,c).
    Also: 3 - n + (a + c + |a-b| + |b-c|) / 2. -/
theorem sbd_3row (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * (3 - min a b - min b c) = 2 * 3 - 2 * min a b - 2 * min b c := by omega

-- The total variation term: TV = Σ|w_{i+1} - w_i| = Σ(max - min) per step.
-- TV for 3 rows: |b - a| + |c - b| = (max(a,b) - min(a,b)) + (max(b,c) - min(b,c))

/-- Kernel verification: S_BD = T - n + (w₀ + w_{T-1} + TV)/2 for specific profiles. -/
-- Profile (3, 3, 3): n=9, T=3, TV=0, w₀=w₂=3. Formula: 3-9+(3+3+0)/2 = -6+3 = -3. 
-- S_BD = 3 - min(3,3) - min(3,3) = 3-3-3 = -3. ✓
example : 3 - (9 : Int) + (3 + 3 + 0) / 2 = -3 := by norm_num

-- Profile (1, 5, 1): n=7, T=3, TV=8, w₀=w₂=1. Formula: 3-7+(1+1+8)/2 = -4+5 = 1.
-- S_BD = 3 - min(1,5) - min(5,1) = 3-1-1 = 1. ✓
example : 3 - (7 : Int) + (1 + 1 + 8) / 2 = 1 := by norm_num

-- Profile (2, 4, 3): n=9, T=3, TV=|4-2|+|3-4|=3, w₀=2, w₂=3. 
-- Formula: 3-9+(2+3+3)/2 = -6+4 = -2.
-- S_BD = 3 - min(2,4) - min(4,3) = 3-2-3 = -2. ✓
example : 3 - (9 : Int) + (2 + 3 + 3) / 2 = -2 := by norm_num

/-! ## General exact BD formula for variable-width grids

We prove the general formula for arbitrary width profiles using lists.
All definitions and the main theorem work over `List ℕ`.

The doubled formula (to avoid division):
  2 · S_BD = 2T - 2n + w₀ + w_{T-1} + TV

where n = Σw_i, T = length, TV = Σ|w_{i+1} - w_i|.

Equivalently, in terms of the components:
  2 · S_BD = 2 · n - 2 · hLinks - 2 · vLinks
  hLinks = n - T
  2 · vLinks = 2n - w₀ - w_{T-1} - TV
-/

/-- Horizontal links: each row of width w contributes w-1 links. -/
def hLinksAux : List ℕ → ℕ
  | [] => 0
  | w :: ws => (w - 1) + hLinksAux ws

/-- Vertical links: between adjacent rows, min(w_i, w_{i+1}) links. -/
def vLinksAux : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | w₁ :: w₂ :: ws => min w₁ w₂ + vLinksAux (w₂ :: ws)

/-- Total variation: Σ (max(w_i, w_{i+1}) - min(w_i, w_{i+1})). -/
def totalVar : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | w₁ :: w₂ :: ws => (max w₁ w₂ - min w₁ w₂) + totalVar (w₂ :: ws)

/-- Sum of adjacent pairs: Σ (w_i + w_{i+1}). -/
def adjSum : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | w₁ :: w₂ :: ws => (w₁ + w₂) + adjSum (w₂ :: ws)

/-- All widths are at least 1. -/
def allPositive (ws : List ℕ) : Prop := ∀ w ∈ ws, 0 < w

/-- hLinksAux + length = sum for positive-width lists.
    Equivalently, hLinks = n - T. -/
theorem hLinksAux_add_length (ws : List ℕ) (hp : allPositive ws) :
    hLinksAux ws + ws.length = ws.sum := by
  induction ws with
  | nil => simp [hLinksAux]
  | cons w ws ih =>
    simp only [hLinksAux, List.sum_cons, List.length_cons]
    have hw : 0 < w := hp w List.mem_cons_self
    have hp' : allPositive ws := fun x hx => hp x (List.mem_cons_of_mem _ hx)
    have := ih hp'
    omega

/-- Key identity: 2 * min(a,b) + (max(a,b) - min(a,b)) = a + b. -/
theorem two_min_add_diff (a b : ℕ) :
    2 * min a b + (max a b - min a b) = a + b := by omega

/-- 2 * vLinksAux + totalVar = adjSum.
    This is the term-by-term application of 2*min(a,b) + (max-min) = a+b. -/
theorem two_vLinks_add_totalVar (ws : List ℕ) :
    2 * vLinksAux ws + totalVar ws = adjSum ws := by
  induction ws with
  | nil => simp [vLinksAux, totalVar, adjSum]
  | cons w ws ih =>
    match ws with
    | [] => simp [vLinksAux, totalVar, adjSum]
    | w₂ :: ws' =>
      simp only [vLinksAux, totalVar, adjSum]
      have key := two_min_add_diff w w₂
      omega

/-- adjSum telescopes: adjSum [w₀, ..., w_{T-1}] + w₀ + w_{T-1} = 2 * sum.
    Stated for lists of length ≥ 2 via pattern matching on w₀ :: w₁ :: rest. -/
theorem adjSum_telescope : ∀ (w₀ w₁ : ℕ) (rest : List ℕ),
    adjSum (w₀ :: w₁ :: rest) + w₀ + (w₁ :: rest).getLast (List.cons_ne_nil _ _) =
    2 * (w₀ :: w₁ :: rest).sum := by
  intro w₀ w₁ rest
  induction rest generalizing w₀ w₁ with
  | nil =>
    simp [adjSum, List.sum_cons, List.getLast_cons]
    omega
  | cons w₂ rest ih =>
    simp only [adjSum, List.sum_cons]
    have ih' := ih w₁ w₂
    simp only [adjSum, List.sum_cons] at ih'
    have : (w₁ :: w₂ :: rest).getLast (List.cons_ne_nil _ _) =
           (w₂ :: rest).getLast (List.cons_ne_nil _ _) := by
      simp [List.getLast_cons]
    rw [this]
    omega

/-- The exact BD formula for variable-width grids.

For ws = [w₀, w₁, ..., w_{T-1}] with each w_i ≥ 1:

  2 · (Σw_i - hLinksAux ws - vLinksAux ws) =
  2 · |ws| - 2 · Σw_i + w₀ + w_{T-1} + totalVar ws

This is the doubled form of S_BD = T - n + (w₀ + w_{T-1} + TV)/2. -/
theorem exact_bd_formula (w₀ w₁ : ℕ) (rest : List ℕ)
    (hp : allPositive (w₀ :: w₁ :: rest)) :
    let ws := w₀ :: w₁ :: rest
    let wLast := (w₁ :: rest).getLast (List.cons_ne_nil _ _)
    2 * (↑(ws.sum) - ↑(hLinksAux ws) - ↑(vLinksAux ws) : ℤ) =
    2 * (ws.length : ℤ) - 2 * ↑(ws.sum) + ↑w₀ + ↑wLast + ↑(totalVar ws) := by
  have h1 := hLinksAux_add_length (w₀ :: w₁ :: rest) hp
  have h2 := two_vLinks_add_totalVar (w₀ :: w₁ :: rest)
  have h3 := adjSum_telescope w₀ w₁ rest
  omega

/-- The 2·vLinks identity: 2·vLinks + w₀ + w_{T-1} + TV = 2n. -/
theorem two_vLinks_identity (w₀ w₁ : ℕ) (rest : List ℕ) :
    let ws := w₀ :: w₁ :: rest
    let wLast := (w₁ :: rest).getLast (List.cons_ne_nil _ _)
    2 * vLinksAux ws + w₀ + wLast + totalVar ws = 2 * ws.sum := by
  have h1 := two_vLinks_add_totalVar (w₀ :: w₁ :: rest)
  have h2 := adjSum_telescope w₀ w₁ rest
  omega

/-- Total variation of a constant list is 0. -/
theorem totalVar_replicate (w : ℕ) : ∀ T, totalVar (List.replicate T w) = 0 := by
  intro T
  induction T with
  | zero => simp [totalVar]
  | succ T' ih =>
    cases T' with
    | zero => simp [totalVar, List.replicate]
    | succ T'' =>
      simp only [List.replicate_succ, totalVar, Nat.max_self, Nat.min_self, Nat.sub_self,
        Nat.zero_add]
      exact ih

/-- Specialization: constant-width grid. All widths equal to w, T ≥ 2 rows.
    S_BD = T - T*w + w = -(T-1)*(w-1) + 1, i.e., 2*S_BD = 2T - 2Tw + 2w. -/
theorem exact_bd_constant_width (w T : ℕ) (hw : 0 < w) (hT : 2 ≤ T) :
    ∃ (w₀ w₁ : ℕ) (rest : List ℕ),
      List.replicate T w = w₀ :: w₁ :: rest ∧
      2 * (↑((w₀ :: w₁ :: rest).sum) - ↑(hLinksAux (w₀ :: w₁ :: rest)) -
        ↑(vLinksAux (w₀ :: w₁ :: rest)) : ℤ) =
      2 * ↑T - 2 * (↑T * ↑w : ℤ) + 2 * ↑w := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 2 := ⟨T - 2, by omega⟩
  refine ⟨w, w, List.replicate T' w, ?_, ?_⟩
  · simp [List.replicate_succ]
  · have hp : allPositive (w :: w :: List.replicate T' w) := by
      intro x hx
      simp only [List.mem_cons, List.mem_replicate] at hx
      obtain rfl | rfl | ⟨-, rfl⟩ := hx <;> exact hw
    have hformula := exact_bd_formula w w (List.replicate T' w) hp
    simp only at hformula
    have hlast : (w :: List.replicate T' w).getLast (List.cons_ne_nil _ _) = w := by
      have hmem := List.getLast_mem (List.cons_ne_nil w (List.replicate T' w))
      rw [List.mem_cons] at hmem
      rcases hmem with h | h
      · exact h
      · exact List.eq_of_mem_replicate h
    have htv : totalVar (w :: w :: List.replicate T' w) = 0 := by
      have := totalVar_replicate w (T' + 2)
      simp [List.replicate_succ] at this
      exact this
    have hsum : (w :: w :: List.replicate T' w).sum = (T' + 2) * w := by
      simp [List.sum_cons, List.sum_replicate, Nat.add_mul]
      ring
    have hlen : (w :: w :: List.replicate T' w).length = T' + 2 := by simp
    rw [hlast, htv, hsum, hlen] at hformula
    push_cast at hformula ⊢
    linarith

/-! ## Physical interpretation

  The exact formula S_BD = T - n + (w₀ + w_{T-1} + TV)/2 decomposes as:

  1. BULK TERM: T - n (always negative for multi-row grids, grows with area)
  2. BOUNDARY TERM: (w₀ + w_{T-1})/2 (depends on the temporal boundary widths)
  3. TOTAL VARIATION: TV/2 (measures the roughness of the profile)

  For the flat grid (constant width w):
    TV = 0, w₀ = w_{T-1} = w.
    S_BD = T - Tw + w = -(T-1)(w-1) + 1. ✓

  For a profile with large variations (rough geometry):
    TV is large → S_BD is less negative → higher energy.

  The positive energy theorem becomes:
    TV ≥ 0 always, so S_BD ≥ T - n + (w₀ + w_{T-1})/2.
    The minimum TV = 0 is achieved only by constant-width profiles.
    For fixed n and T: constant width w = n/T gives S_BD = -(T-1)(n/T-1)+1.

  CONNECTION TO JT GRAVITY:
  The JT regression (R² ≈ 0.75) arises because R and LogSch approximate TV:
    R = Σ(w_{i+1} - 2w_i + w_{i-1}) ≈ second derivative (curvature)
    LogSch = Σ(log w_{i+1} - log w_i)² ≈ squared log-derivative
    TV = Σ|w_{i+1} - w_i| = first derivative in L¹ norm
  These are related (rough profiles have large R, LogSch, AND TV)
  but the exact functional is TV, not R or LogSch.

  This is STRONGER than the JT regression: instead of an approximate fit
  to curvature + Schwarzian, we have the EXACT functional (total variation).
-/

end CausalAlgebraicGeometry.ExactBDFormula
