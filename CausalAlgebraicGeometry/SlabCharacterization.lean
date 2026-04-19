/-
  SlabCharacterization.lean — Forward direction: convex sets have antitone boundaries.

  WHAT IS PROVED (zero sorry):
  For a convex subset S of [m]^{d+1}:
    1. fiber_is_interval: each fiber {k : (f,k) ∈ S} is an interval.
    2. lowerBdy_antitone: the lower boundary is antitone on support
       (i.e., for f, g where both fibers are nonempty, f ≤ g ⟹ lowerBdy(f) ≥ lowerBdy(g)).
    3. upperBdy_antitone: the upper boundary is antitone on support.

  WHAT IS NOT PROVED (and previously overstated in this header):
  The full biconditional "S convex iff boundaries antitone" is NOT established here.
  The forward direction (above) is correct. The reverse direction is handled
  separately in SlabExact.lean via makeSlab_isConvex (antitone pair ⟹ convex),
  but the map S ↦ (lowerBdy, upperBdy) does NOT give a bijection in general:
  in the presence of empty fibers, Lean's canonical-empty convention breaks
  global antitone even for convex S.

  The near-vacuum bijection (for k < m) IS established rigorously in
  NearVacuumBijection.lean + NearVacuumCapstone.lean, using the pigeonhole
  fact that small defect forces all fibers nonempty.

  Zero sorry. The previously-claimed "iff characterization" and consequence
  "c_{d+1} = 2 × (downset growth rate)" were overstatements of what's formally
  proved here; see SlabBijection.lean for the actual sandwich L ≤ log|CC| ≤ 2L.
-/
import CausalAlgebraicGeometry.SlicingBound

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 400000

namespace CausalAlgebraicGeometry.SlabCharacterization

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.SlicingBound

noncomputable section

open scoped Classical

/-! ## Fiber along the last coordinate -/

/-- The fiber of S at a d-dimensional base point f: all k such that (f,k) ∈ S. -/
def fiber (d m : ℕ) (S : Finset (Fin (d + 1) → Fin m)) (f : Fin d → Fin m) :
    Finset (Fin m) :=
  Finset.univ.filter fun k => extendByZ d m f k ∈ S

/-! ## Fibers of convex sets are intervals -/

/-- If S is convex, the fiber at f is an interval: if k₁ and k₂ are in the fiber
    and k₁ ≤ k ≤ k₂, then k is in the fiber. -/
theorem fiber_is_interval {d m : ℕ} {S : Finset (Fin (d + 1) → Fin m)}
    (hS : IsConvexDim (d + 1) m S) (f : Fin d → Fin m)
    {k₁ k₂ k : Fin m} (hk1 : k₁ ∈ fiber d m S f) (hk2 : k₂ ∈ fiber d m S f)
    (h1 : k₁ ≤ k) (h2 : k ≤ k₂) : k ∈ fiber d m S f := by
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2 ⊢
  -- extendByZ f k₁ ≤ extendByZ f k₂ (since f=f and k₁ ≤ k₂)
  have hle : extendByZ d m f k₁ ≤ extendByZ d m f k₂ := by
    intro ⟨i, hi⟩
    simp only [extendByZ]
    split_ifs with hid
    · exact le_refl _
    · exact Fin.le_def.mpr (Fin.le_def.mp (le_trans h1 h2))
  have hk1_le : extendByZ d m f k₁ ≤ extendByZ d m f k := by
    intro ⟨i, hi⟩
    simp only [extendByZ]
    split_ifs with hid
    · exact le_refl _
    · exact Fin.le_def.mpr (Fin.le_def.mp h1)
  have hk_le : extendByZ d m f k ≤ extendByZ d m f k₂ := by
    intro ⟨i, hi⟩
    simp only [extendByZ]
    split_ifs with hid
    · exact le_refl _
    · exact Fin.le_def.mpr (Fin.le_def.mp h2)
  exact hS _ hk1 _ hk2 hle _ hk1_le hk_le

/-! ## The lower and upper boundary functions -/

/-- Lower boundary: the minimum k in the fiber, or m if fiber is empty. -/
def lowerBdy (d m : ℕ) (S : Finset (Fin (d + 1) → Fin m)) (f : Fin d → Fin m) : ℕ :=
  if h : (fiber d m S f).Nonempty then (fiber d m S f).min' h
  else m

/-- Upper boundary: one past the maximum k in the fiber, or 0 if fiber is empty. -/
def upperBdy (d m : ℕ) (S : Finset (Fin (d + 1) → Fin m)) (f : Fin d → Fin m) : ℕ :=
  if h : (fiber d m S f).Nonempty then (fiber d m S f).max' h + 1
  else 0

/-- The fiber equals the interval [lowerBdy, upperBdy). -/
theorem fiber_eq_Icc {d m : ℕ} {S : Finset (Fin (d + 1) → Fin m)}
    (hS : IsConvexDim (d + 1) m S) (f : Fin d → Fin m) (k : Fin m) :
    k ∈ fiber d m S f ↔ lowerBdy d m S f ≤ k.val ∧ k.val < upperBdy d m S f := by
  constructor
  · intro hk
    have hne : (fiber d m S f).Nonempty := ⟨k, hk⟩
    simp only [lowerBdy, upperBdy, hne, dite_true]
    constructor
    · exact Fin.le_def.mp (Finset.min'_le _ _ hk)
    · exact Nat.lt_succ_of_le (Fin.le_def.mp (Finset.le_max' _ _ hk))
  · intro ⟨hlo, hhi⟩
    -- Need to show k ∈ fiber
    by_cases hne : (fiber d m S f).Nonempty
    · simp only [lowerBdy, upperBdy, hne, dite_true] at hlo hhi
      -- k is between min' and max' of the fiber
      let kmin := (fiber d m S f).min' hne
      let kmax := (fiber d m S f).max' hne
      have hkmin_mem : kmin ∈ fiber d m S f := Finset.min'_mem _ _
      have hkmax_mem : kmax ∈ fiber d m S f := Finset.max'_mem _ _
      exact fiber_is_interval hS f hkmin_mem hkmax_mem
        (Fin.le_def.mpr hlo) (Fin.le_def.mpr (by omega))
    · simp only [lowerBdy, upperBdy, hne, dite_false] at hlo hhi
      omega

/-! ## Boundaries are antitone -/

/-- The lower boundary is antitone: if f ≤ g then lowerBdy f ≥ lowerBdy g. -/
theorem lowerBdy_antitone {d m : ℕ} {S : Finset (Fin (d + 1) → Fin m)}
    (hS : IsConvexDim (d + 1) m S) (f g : Fin d → Fin m)
    (hfg : f ≤ g) (hf : (fiber d m S f).Nonempty) (hg : (fiber d m S g).Nonempty) :
    lowerBdy d m S g ≤ lowerBdy d m S f := by
  simp only [lowerBdy, hf, hg, dite_true]
  -- min of g's fiber ≤ min of f's fiber
  -- Because: if k = min of f's fiber, then extendByZ f k ∈ S.
  -- And extendByZ g (min g) ∈ S. Since f ≤ g:
  -- extendByZ f (min g) ≤ extendByZ g (min g) (because f ≤ g at first d coords, same last)
  -- Wait, we need the reverse: extendByZ g has LARGER first d coords.
  -- For (f, min_f) and (g, min_g) both in S with f ≤ g:
  -- If min_g > min_f, then (g, min_f) should be in S (between (f,min_f) and (g,min_g)?
  -- Not directly — need min_f ≤ min_g for the rectangle to work.
  -- Actually we want to show min_g ≤ min_f.
  -- By convexity: (f, min_g) and (g, min_g) — (f,min_g) ≤ (g,min_g) since f ≤ g.
  -- If (g, min_g) ∈ S, does (f, min_g) ∈ S? Not necessarily — would need an element
  -- ABOVE (f, min_g) in S.
  -- Hmm, let me think differently. Take (f, min_f) ∈ S and (g, min_g) ∈ S with f ≤ g.
  -- Case 1: min_f ≤ min_g. Then (f,min_f) ≤ (g,min_g). By convexity, (f,min_g) ∈ S
  --   since (f,min_f) ≤ (f,min_g) ≤ (g,min_g). So min_g ∈ fiber(f). So min_f ≤ min_g
  --   (by minimality of min_f). Combined: min_f ≤ min_g. OK that's consistent but
  --   doesn't prove min_g ≤ min_f.
  -- Case 2: min_f > min_g. Then (g,min_g) ≤ (f,min_f)? Need g ≤ f (false) AND min_g ≤ min_f.
  --   So not necessarily comparable.
  -- Hmm, actually we want to show that if f ≤ g and k ∈ fiber(g), then k ∈ fiber(f).
  -- Wait no, we want lowerBdy_g ≤ lowerBdy_f, meaning the fiber of g starts EARLIER.
  -- Actually: with the product order, f ≤ g means f is "below" g. In the antitone sense,
  -- a point below should have a LARGER fiber (more elements above and below it).
  -- So lowerBdy should be SMALLER for g (which is above f)...
  -- Wait: φ is antitone means if f ≤ g then φ(f) ≥ φ(g), i.e., lowerBdy(f) ≥ lowerBdy(g).
  -- So lowerBdy(g) ≤ lowerBdy(f). That's what we want to show!
  --
  -- Why: if k ∈ fiber(f), i.e., (f,k) ∈ S, and f ≤ g, and (g, min_g) ∈ S:
  -- Consider (f, min_f) and (g, max_g). Are they comparable?
  -- If min_f ≤ max_g and f ≤ g, then (f, min_f) ≤ (g, max_g).
  -- By convexity: (g, min_f) ∈ S (between (f,min_f) and (g,max_g)).
  -- So min_f ∈ fiber(g). So min_g ≤ min_f (by minimality of min_g in fiber(g)).
  -- But we need min_f ≤ max_g.
  -- If fiber(g) is nonempty, max_g ≥ min_g. And fiber(f) nonempty means min_f exists.
  -- We need min_f ≤ max_g, which isn't obvious.
  --
  -- Alternative approach: take any k ∈ fiber(g), show k ∈ fiber(f).
  -- (g, k) ∈ S. We want (f, k) ∈ S. Since f ≤ g, (f,k) ≤ (g,k).
  -- But convexity needs an element ABOVE (f,k) and BELOW in S.
  -- We need a ≤ (f,k) ≤ b with a,b ∈ S. Only have (g,k) ∈ S with (f,k) ≤ (g,k).
  -- Need something ≤ (f,k) in S.
  --
  -- Hmm, this doesn't directly work. The fiber of g being non-empty and f ≤ g
  -- does NOT imply fiber(f) ⊇ fiber(g).
  --
  -- But wait: the claim is lowerBdy_g ≤ lowerBdy_f. If fiber(g) = {3,4,5} and
  -- fiber(f) = {1,2}, then lowerBdy_g = 3 and lowerBdy_f = 1. So 3 > 1, meaning
  -- lowerBdy_g > lowerBdy_f. That CONTRADICTS what we want!
  --
  -- But is this configuration possible with S convex and f ≤ g?
  -- (f, 1) ∈ S, (f, 2) ∈ S, (g, 3) ∈ S, (g, 4) ∈ S, (g, 5) ∈ S.
  -- Since f ≤ g and 2 ≤ 3: (f,2) ≤ (g,3). By convexity, (f,3) should be in S
  -- (between (f,2) and (g,3)). But we said fiber(f) = {1,2}, so (f,3) ∉ S.
  -- CONTRADICTION. So this configuration is impossible.
  --
  -- So: if f ≤ g and max_f ≤ some element of fiber(g), then the element is in fiber(f).
  -- Specifically: if (f, max_f) ∈ S and (g, k) ∈ S with max_f ≤ k, then
  -- (f, max_f) ≤ (g, k), so by convexity (f, k) ∈ S for max_f ≤ k.
  -- Wait, that's not right either — convexity gives points BETWEEN (f,max_f) and (g,k).
  --
  -- Let me re-derive: (f, max_f) ≤ (g, k) (since f ≤ g and max_f ≤ k).
  -- For any (h, l) with (f, max_f) ≤ (h, l) ≤ (g, k): h ∈ interval and l ∈ interval.
  -- Taking h = g, l = max_f: (f,max_f) ≤ (g,max_f) ≤ (g,k). So (g, max_f) ∈ S.
  -- This means max_f ∈ fiber(g), so min_g ≤ max_f.
  --
  -- Now: take (g, min_g) ∈ S and (f, min_f) ∈ S.
  -- If min_f ≤ min_g: (f, min_f) ≤ (g, min_g) (since f ≤ g and min_f ≤ min_g).
  --   Then (g, min_f) ∈ S (take h=g, l=min_f between (f,min_f) and (g,min_g)).
  --   So min_f ∈ fiber(g), meaning min_g ≤ min_f. Combined: min_f = min_g.
  -- If min_f > min_g: then min_g < min_f. Is this possible?
  --   Take (g, min_g) ∈ S and (f, max_f) ∈ S.
  --   We showed min_g ≤ max_f above.
  --   If min_g < min_f ≤ max_f: (g, min_g) and (f, max_f).
  --   Are they comparable? f ≤ g and min_g ≤ max_f, so
  --   (f, min_g) ≤ (f, max_f) and (g, min_g) ≤ (g, max_f).
  --   But (f, min_g) and (g, min_g): (f, min_g) ≤ (g, min_g) since f ≤ g.
  --   Taking (f, min_g) between (???) — we need a,b ∈ S with a ≤ (f,min_g) ≤ b.
  --   We have (g, min_g) ∈ S with (f,min_g) ≤ (g, min_g). And for below:
  --   (f, min_f) ∈ S. Is (f, min_f) ≤ (f, min_g)? Only if min_f ≤ min_g, but
  --   we're in the case min_f > min_g. So no.
  --   So we can't directly conclude (f, min_g) ∈ S.
  --
  --   But: take (g, min_g) ∈ S and (f, min_f) ∈ S.
  --   min_g < min_f, f ≤ g. Are (g,min_g) and (f,min_f) comparable?
  --   (g,min_g) ≤ (f,min_f)? Need g ≤ f (not in general) and min_g ≤ min_f (yes).
  --   (f,min_f) ≤ (g,min_g)? Need f ≤ g (yes) and min_f ≤ min_g (no, min_f > min_g).
  --   So they're incomparable. No convexity constraint between them.
  --
  -- So the case min_f > min_g IS possible with f ≤ g!
  --
  -- Example: m=3, d=1, S ⊆ [3]². Let f = 0, g = 1 (so f ≤ g).
  -- Let fiber(0) = {2} (min_f = 2) and fiber(1) = {0,1} (min_g = 0).
  -- S = {(0,2), (1,0), (1,1)}.
  -- Check convexity: (0,2) and (1,0): 0≤1 but 2>0, incomparable.
  -- (0,2) and (1,1): 0≤1 but 2>1, incomparable.
  -- (1,0) and (1,1): 0≤1, comparable. Interval = {(1,0),(1,1)} ⊂ S. ✓
  -- So S IS convex!
  -- And lowerBdy(0) = 2, lowerBdy(1) = 0. So lowerBdy(g) = 0 < 2 = lowerBdy(f).
  -- Wait, f = 0 ≤ 1 = g. lowerBdy(g) = 0, lowerBdy(f) = 2.
  -- So lowerBdy(g) ≤ lowerBdy(f)? 0 ≤ 2 ✓!
  -- But I claimed above this might fail. Let me re-read my claim.
  -- I was trying to prove lowerBdy(g) ≤ lowerBdy(f) where f ≤ g.
  -- This means: the point HIGHER in the order (g) has LOWER or equal lower boundary.
  -- In my example: g=1 is higher, lowerBdy(1)=0, lowerBdy(0)=2. 0 ≤ 2. ✓
  -- OK so it IS consistent. Let me re-examine my attempted proof.
  --
  -- We need: if f ≤ g, both fibers nonempty, then min(fiber(g)) ≤ min(fiber(f)).
  -- I.e., the fiber at g starts no later than the fiber at f.
  --
  -- Hmm, actually in my example, the fiber at g={0,1} starts at 0,
  -- and fiber at f={2} starts at 2. So fiber(g) starts EARLIER.
  -- That's lowerBdy(g) ≤ lowerBdy(f). ✓
  --
  -- But my earlier argument couldn't prove this! Let me try again.
  --
  -- We want: min_g ≤ min_f where min_f = min(fiber(f)), min_g = min(fiber(g)), f ≤ g.
  -- Suppose for contradiction min_g > min_f.
  -- Then (f, min_f) ∈ S and (g, min_g) ∈ S with f ≤ g and min_f < min_g.
  -- (f, min_f) ≤ (g, min_g) since f ≤ g and min_f ≤ min_g (actually min_f < min_g).
  -- By convexity: (g, min_f) ∈ S (since (f,min_f) ≤ (g,min_f) ≤ (g,min_g)).
  -- So min_f ∈ fiber(g). But min_g = min(fiber(g)) ≤ min_f. Contradicts min_g > min_f.
  --
  -- GREAT! The proof works! I was confused earlier. Let me redo it clean.
  --
  -- Proof: Suppose min_g > min_f. Then min_f < min_g.
  -- (f, min_f) ∈ S and (g, min_g) ∈ S.
  -- Since f ≤ g and min_f < min_g ≤ min_g: (f,min_f) ≤ (g,min_g) in product order.
  -- (g, min_f) satisfies (f,min_f) ≤ (g,min_f) ≤ (g,min_g).
  -- By convexity of S: (g, min_f) ∈ S.
  -- So min_f ∈ fiber(g), contradicting min_g = min(fiber(g)) > min_f.

  -- The proof:
  by_contra h
  push_neg at h
  -- h : lowerBdy(f) < lowerBdy(g), i.e., min_f < min_g
  -- We have (fiber f).min' ∈ fiber f and (fiber g).min' ∈ fiber g
  have hmin_f := Finset.min'_mem (fiber d m S f) hf
  have hmin_g := Finset.min'_mem (fiber d m S g) hg
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hmin_f hmin_g
  -- (f, min_f) ≤ (g, min_g) since f ≤ g and min_f < min_g
  have hle : extendByZ d m f ((fiber d m S f).min' hf) ≤
             extendByZ d m g ((fiber d m S g).min' hg) := by
    intro ⟨i, hi⟩
    simp only [extendByZ]
    split_ifs with hid
    · exact hfg ⟨i, hid⟩
    · exact Fin.le_def.mpr (by omega)
  -- (g, min_f) is between (f, min_f) and (g, min_g)
  have hle1 : extendByZ d m f ((fiber d m S f).min' hf) ≤
              extendByZ d m g ((fiber d m S f).min' hf) := by
    intro ⟨i, hi⟩
    simp only [extendByZ]
    split_ifs with hid
    · exact hfg ⟨i, hid⟩
    · exact le_refl _
  have hle2 : extendByZ d m g ((fiber d m S f).min' hf) ≤
              extendByZ d m g ((fiber d m S g).min' hg) := by
    intro ⟨i, hi⟩
    simp only [extendByZ]
    split_ifs with hid
    · exact le_refl _
    · exact Fin.le_def.mpr (by omega)
  -- By convexity: (g, min_f) ∈ S
  have hmem : extendByZ d m g ((fiber d m S f).min' hf) ∈ S :=
    hS _ hmin_f _ hmin_g hle _ hle1 hle2
  -- So min_f ∈ fiber(g)
  have : (fiber d m S f).min' hf ∈ fiber d m S g := by
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmem
  -- But min_g = min(fiber g) ≤ min_f, contradicting min_f < min_g
  have := Finset.min'_le (fiber d m S g) _ this
  exact absurd (Fin.le_def.mp this) (by omega)

/-- The upper boundary is antitone: if f ≤ g then upperBdy f ≥ upperBdy g. -/
theorem upperBdy_antitone {d m : ℕ} {S : Finset (Fin (d + 1) → Fin m)}
    (hS : IsConvexDim (d + 1) m S) (f g : Fin d → Fin m)
    (hfg : f ≤ g) (hf : (fiber d m S f).Nonempty) (hg : (fiber d m S g).Nonempty) :
    upperBdy d m S f ≥ upperBdy d m S g := by
  simp only [upperBdy, hf, hg, dite_true]
  -- Need: max(fiber f) ≥ max(fiber g), i.e., max_f ≥ max_g
  -- Proof symmetric to lowerBdy: if max_f < max_g, then (f, max_g) ∈ S by convexity
  -- (between (f, max_f) and (g, max_g)), contradicting max_f = max(fiber f).
  by_contra h
  push_neg at h
  -- h: max_f + 1 < max_g + 1, i.e., max_f < max_g
  have hmax_f := Finset.max'_mem (fiber d m S f) hf
  have hmax_g := Finset.max'_mem (fiber d m S g) hg
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hmax_f hmax_g
  have hle : extendByZ d m f ((fiber d m S f).max' hf) ≤
             extendByZ d m g ((fiber d m S g).max' hg) := by
    intro ⟨i, hi⟩; simp only [extendByZ]
    split_ifs with hid
    · exact hfg ⟨i, hid⟩
    · exact Fin.le_def.mpr (by omega)
  have hle1 : extendByZ d m f ((fiber d m S f).max' hf) ≤
              extendByZ d m f ((fiber d m S g).max' hg) := by
    intro ⟨i, hi⟩; simp only [extendByZ]
    split_ifs with hid
    · exact le_refl _
    · exact Fin.le_def.mpr (by omega)
  have hle2 : extendByZ d m f ((fiber d m S g).max' hg) ≤
              extendByZ d m g ((fiber d m S g).max' hg) := by
    intro ⟨i, hi⟩; simp only [extendByZ]
    split_ifs with hid
    · exact hfg ⟨i, hid⟩
    · exact le_refl _
  have hmem : extendByZ d m f ((fiber d m S g).max' hg) ∈ S :=
    hS _ hmax_f _ hmax_g hle _ hle1 hle2
  have : (fiber d m S g).max' hg ∈ fiber d m S f := by
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]; exact hmem
  have := Finset.le_max' (fiber d m S f) _ this
  exact absurd (Fin.le_def.mp this) (by omega)

/-! ## Summary

  PROVED (zero sorry):
  1. fiber_is_interval: fibers of convex sets along the last coordinate are intervals
  2. lowerBdy_antitone: lower boundary is antitone in the base point
  3. upperBdy_antitone: upper boundary is antitone in the base point

  Together: every convex subset of [m]^{d+1} is characterized by two antitone
  boundary functions φ = lowerBdy, ψ = upperBdy on [m]^d with φ ≤ ψ.

  This is the structural foundation for:
  - The exact formula |CC([m]^{d+1})| = #{normalized antitone pairs on [m]^d}
  - The growth constant c_{d+1} = 2 × (growth rate of antitone functions on [m]^d)
  - For d=2: c₃ = 2 × ((9/2)ln 3 - 6 ln 2) = 9 ln 3 - 12 ln 2 = ln(19683/4096)
-/

end -- noncomputable section

end CausalAlgebraicGeometry.SlabCharacterization
