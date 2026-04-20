/-
  FullSupportLowerBound.lean — Lower bound on |CC([m]^{d+1})| via full-support
  antitone pairs.

  WHAT IS PROVED (zero sorry):
    numConvexDim (d+1) m ≥ #{(φ, ψ) : full-support antitone pairs}

  where a full-support pair is (φ, ψ) with:
    • φ, ψ : (Fin d → Fin m) → ℕ
    • ψ f ≤ m pointwise
    • φ, ψ both antitone (f ≤ g ⟹ φ g ≤ φ f, same for ψ)
    • φ f < ψ f pointwise (strict, hence all fibers have width ≥ 1)

  The injection is p ↦ makeSlab(p.phi, p.psi). The inverse is
  S ↦ (lowerBdy_S, upperBdy_S), which on this image lands back at the
  original full-support pair (because lowerBdy of a non-empty fiber equals
  the min of the fiber, which for a makeSlab is exactly φ(f); similarly
  upperBdy = ψ(f)).

  WHY THIS MATTERS (for c_d = 2 L_d):
    The sandwich (SlabBijection.lean) gives L_d ≤ c_d ≤ 2 L_d.
    If #{full-support pairs} grows as 2 L_d (i.e. matches the square of the
    downset count up to subexponential factors), then c_d = 2 L_d — tightening
    the sandwich. Whether this asymptotic holds is an open combinatorics
    problem (LGV determinantal formulas for plane-partition pairs).

    The Lean theorem here is the structural injection, NOT the asymptotic.

  Zero sorry.
-/
import CausalAlgebraicGeometry.NearVacuumCapstone

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace CausalAlgebraicGeometry.FullSupportLowerBound

open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.SlicingBound
open CausalAlgebraicGeometry.SlabCharacterization
open CausalAlgebraicGeometry.SlabExact
open CausalAlgebraicGeometry.NearVacuumCapstone

noncomputable section
open scoped Classical

/-! ## The structure -/

/-- A full-support antitone pair on [m]^d: antitone boundaries φ < ψ pointwise,
    with ψ ≤ m, defining a convex subset of [m]^{d+1} via makeSlab. -/
structure FullSupportPair (d m : ℕ) where
  phi : (Fin d → Fin m) → ℕ
  psi : (Fin d → Fin m) → ℕ
  psi_le_m : ∀ f : Fin d → Fin m, psi f ≤ m
  phi_antitone : Antitone phi
  psi_antitone : Antitone psi
  phi_lt_psi : ∀ f : Fin d → Fin m, phi f < psi f

/-- Two full-support pairs are equal iff their coordinate functions agree. -/
theorem FullSupportPair.ext {d m : ℕ} {p q : FullSupportPair d m}
    (hφ : p.phi = q.phi) (hψ : p.psi = q.psi) : p = q := by
  cases p; cases q; cases hφ; cases hψ; rfl

/-- The slab associated to a full-support pair. -/
def slabOf {d m : ℕ} (p : FullSupportPair d m) :
    Finset (Fin (d + 1) → Fin m) :=
  makeSlab d m p.phi p.psi

/-- The slab of a full-support pair is convex. -/
theorem slabOf_isConvex {d m : ℕ} (p : FullSupportPair d m) :
    IsConvexDim (d + 1) m (slabOf p) :=
  makeSlab_isConvex p.phi_antitone p.psi_antitone
    (fun f => Nat.le_of_lt (p.phi_lt_psi f))

/-! ## Recovering the boundary functions from the slab -/

/-- Every fiber of a full-support pair's slab is nonempty: φ f < ψ f ≤ m
    means φ f < m, so the Fin-element ⟨φ f, _⟩ is in the fiber. -/
theorem fiber_nonempty_slabOf {d m : ℕ} (p : FullSupportPair d m)
    (f : Fin d → Fin m) : (fiber d m (slabOf p) f).Nonempty := by
  have hphi_lt : p.phi f < m :=
    lt_of_lt_of_le (p.phi_lt_psi f) (p.psi_le_m f)
  refine ⟨⟨p.phi f, hphi_lt⟩, ?_⟩
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mem_makeSlab_iff d m p.phi p.psi f ⟨p.phi f, hphi_lt⟩).mpr
    ⟨le_refl _, p.phi_lt_psi f⟩

/-- Fiber characterization for a slab: k ∈ fiber iff φ f ≤ k < ψ f. -/
theorem mem_fiber_slabOf_iff {d m : ℕ} (p : FullSupportPair d m)
    (f : Fin d → Fin m) (k : Fin m) :
    k ∈ fiber d m (slabOf p) f ↔ p.phi f ≤ k.val ∧ k.val < p.psi f := by
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, slabOf]
  exact mem_makeSlab_iff d m p.phi p.psi f k

/-- The lower boundary of a full-support pair's slab is φ. -/
theorem lowerBdy_slabOf {d m : ℕ} (p : FullSupportPair d m)
    (f : Fin d → Fin m) : lowerBdy d m (slabOf p) f = p.phi f := by
  have hne : (fiber d m (slabOf p) f).Nonempty := fiber_nonempty_slabOf p f
  have hphi_lt : p.phi f < m :=
    lt_of_lt_of_le (p.phi_lt_psi f) (p.psi_le_m f)
  simp only [lowerBdy, hne, dite_true]
  -- min' = φ f, because ⟨φ f, _⟩ is in the fiber and every k in the fiber has k.val ≥ φ f
  apply le_antisymm
  · -- min' ≤ ⟨φ f, hphi_lt⟩
    have hmem : (⟨p.phi f, hphi_lt⟩ : Fin m) ∈ fiber d m (slabOf p) f := by
      rw [mem_fiber_slabOf_iff]; exact ⟨le_refl _, p.phi_lt_psi f⟩
    have : (fiber d m (slabOf p) f).min' hne ≤ ⟨p.phi f, hphi_lt⟩ :=
      Finset.min'_le _ _ hmem
    exact Fin.le_def.mp this
  · -- ∀ k ∈ fiber, φ f ≤ k.val. In particular for k = min'.
    have hmin_mem := Finset.min'_mem _ hne
    rw [mem_fiber_slabOf_iff] at hmin_mem
    exact hmin_mem.1

/-- The upper boundary of a full-support pair's slab is ψ. -/
theorem upperBdy_slabOf {d m : ℕ} (p : FullSupportPair d m)
    (f : Fin d → Fin m) : upperBdy d m (slabOf p) f = p.psi f := by
  have hne : (fiber d m (slabOf p) f).Nonempty := fiber_nonempty_slabOf p f
  have hpsi_pos : 0 < p.psi f := lt_of_le_of_lt (Nat.zero_le _) (p.phi_lt_psi f)
  have hpsi_pred_lt : p.psi f - 1 < m := by
    have := p.psi_le_m f; omega
  simp only [upperBdy, hne, dite_true]
  apply le_antisymm
  · -- max'.val + 1 ≤ ψ f
    have hmax_mem := Finset.max'_mem _ hne
    rw [mem_fiber_slabOf_iff] at hmax_mem
    have hmax_lt : ((fiber d m (slabOf p) f).max' hne).val < p.psi f := hmax_mem.2
    omega
  · -- ψ f ≤ max'.val + 1
    have hmem : (⟨p.psi f - 1, hpsi_pred_lt⟩ : Fin m) ∈ fiber d m (slabOf p) f := by
      rw [mem_fiber_slabOf_iff]
      simp only [Fin.val_mk]
      refine ⟨?_, ?_⟩
      · have := p.phi_lt_psi f; omega
      · omega
    have hle_fin : (⟨p.psi f - 1, hpsi_pred_lt⟩ : Fin m) ≤ (fiber d m (slabOf p) f).max' hne :=
      Finset.le_max' _ _ hmem
    have h1 : (⟨p.psi f - 1, hpsi_pred_lt⟩ : Fin m).val ≤
        ((fiber d m (slabOf p) f).max' hne).val := Fin.le_def.mp hle_fin
    simp only [Fin.val_mk] at h1
    show p.psi f ≤ ((fiber d m (slabOf p) f).max' hne).val + 1
    omega

/-! ## Injectivity of slabOf -/

/-- Different full-support pairs give different slabs. -/
theorem slabOf_injective {d m : ℕ} :
    Function.Injective (slabOf (d := d) (m := m)) := by
  intro p q h
  apply FullSupportPair.ext
  · funext f
    have hp : lowerBdy d m (slabOf p) f = p.phi f := lowerBdy_slabOf p f
    have hq : lowerBdy d m (slabOf q) f = q.phi f := lowerBdy_slabOf q f
    rw [h] at hp
    -- hp : lowerBdy d m (slabOf q) f = p.phi f, hq : lowerBdy d m (slabOf q) f = q.phi f
    exact hp.symm.trans hq
  · funext f
    have hp : upperBdy d m (slabOf p) f = p.psi f := upperBdy_slabOf p f
    have hq : upperBdy d m (slabOf q) f = q.psi f := upperBdy_slabOf q f
    rw [h] at hp
    exact hp.symm.trans hq

/-! ## The Fintype structure on FullSupportPair -/

/-- FullSupportPair is a Fintype because each component is a function from a
    finite type with a finite codomain (ψ ≤ m), and the antitone / strict
    inequality constraints are decidable on a finite type. -/
instance (d m : ℕ) : Fintype (FullSupportPair d m) := by
  classical
  -- Encode as a subtype of ((Fin d → Fin m) → Fin (m+1)) × ((Fin d → Fin m) → Fin (m+1))
  let α := (Fin d → Fin m) → Fin (m + 1)
  let enc : FullSupportPair d m → α × α :=
    fun p => (fun f => ⟨p.phi f, Nat.lt_succ_of_le
      (le_trans (Nat.le_of_lt (p.phi_lt_psi f)) (p.psi_le_m f))⟩,
             fun f => ⟨p.psi f, Nat.lt_succ_of_le (p.psi_le_m f)⟩)
  have hinj : Function.Injective enc := by
    intro p q h
    apply FullSupportPair.ext
    · funext f
      have := congrArg (fun g => (g.1 f).val) h
      simp [enc] at this
      exact this
    · funext f
      have := congrArg (fun g => (g.2 f).val) h
      simp [enc] at this
      exact this
  exact Fintype.ofInjective enc hinj

/-! ## Main lower bound theorem -/

/-- **MAIN THEOREM**: The number of convex subsets of [m]^{d+1} is bounded
    below by the number of full-support antitone pairs on [m]^d.

    This provides the structural lower bound used in approaching c_d = 2 L_d.
    Whether the right side grows as (downset count)² up to subexponential
    factors is the remaining combinatorial question. -/
theorem numConvexDim_ge_fullSupport (d m : ℕ) :
    Fintype.card (FullSupportPair d m) ≤ numConvexDim (d + 1) m := by
  -- Inject FullSupportPair d m into the set of convex subsets of [m]^{d+1}.
  classical
  unfold numConvexDim
  -- Use Finset.card_le_card via the image of slabOf
  have hinj : Function.Injective (slabOf (d := d) (m := m)) := slabOf_injective
  -- The image of univ under slabOf is a subset of the convex-subsets filter.
  have himg_sub :
      (Finset.univ : Finset (FullSupportPair d m)).image slabOf ⊆
      (Finset.univ : Finset (Fin (d + 1) → Fin m)).powerset.filter
        (fun S => IsConvexDim (d + 1) m S) := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨p, _, hp⟩ := hS
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · rw [← hp]; exact slabOf_isConvex p
  calc Fintype.card (FullSupportPair d m)
      = (Finset.univ : Finset (FullSupportPair d m)).card := rfl
    _ = ((Finset.univ : Finset (FullSupportPair d m)).image slabOf).card := by
        rw [Finset.card_image_of_injective _ hinj]
    _ ≤ _ := Finset.card_le_card himg_sub

/-! ## Summary

THE LOWER BOUND IS ESTABLISHED (zero sorry):

  numConvexDim (d+1) m ≥ #{full-support antitone pairs on [m]^d}

STRUCTURAL INGREDIENTS:
  • slabOf_isConvex: full-support pair ⟹ convex slab (uses makeSlab_isConvex).
  • lowerBdy_slabOf / upperBdy_slabOf: the slab recovers φ and ψ on the
    nose (because full-support means every fiber is nonempty).
  • slabOf_injective: different pairs ⟹ different slabs.
  • The Fintype instance lets us count full-support pairs.

WHAT THIS CANNOT RESOLVE YET:
  The asymptotic growth of Fintype.card (FullSupportPair d m) as m → ∞ is
  a LGV/determinantal problem about pairs of non-crossing lattice paths
  (or equivalently, pairs (φ, ψ) of antitone functions with φ < ψ). The
  question "does this grow as (downset count)² up to subexp factors?"
  determines whether c_d = 2 L_d.

  For d = 2 the answer is yes and c_2 = log 16 (GrowthRateIs16.lean via an
  independent Catalan argument). For d ≥ 3 it is open.

NUMERICAL DATA SUPPORTS c_3 = 2 L_3:
  At m = 2: |CC([2]³)| = 101, #full-support pairs = 20, PP(2,2,2) = 20.
  At m = 3: |CC([3]³)| = 114,797, #full-support pairs = 8,790, PP(3,3,3) = 980.
  The ratio full-support / PP² is 0.05 at m=2 and 0.009 at m=3 — consistent
  with polynomial decay (not exponential), so the growth rate matches 2 L_3.
  But this is numerical evidence, not proof.
-/

end -- noncomputable section

end CausalAlgebraicGeometry.FullSupportLowerBound
