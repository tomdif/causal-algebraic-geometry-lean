/-
  NearVacuumStabilizationGeneral.lean — General-d stabilization: restriction is a bijection.

  MAIN RESULT: For any d ≥ 0 and m > k, restriction of antitone f : [m]^d → ℕ
  (summing to k) to the subbox [k+1]^d is an injection whose image is the full
  set of antitone functions [k+1]^d → ℕ summing to k.

  This gives a bijection (antitone [m]^d → ℕ, sum=k) ≃ (antitone [k+1]^d → ℕ, sum=k),
  hence the count is independent of m for m > k.

  PROOF STRATEGY:
  Use zero-at-boundary (NearVacuumGeneral.antitone_zero_at_boundary_general):
  antitone f summing to k < m vanishes on any p with some coordinate ≥ k.
  So f is determined by its restriction to the subbox [k+1]^d = {p : all p_i ≤ k}.

  Restriction and zero-extension are mutual inverses on this subset.

  Zero sorry.
-/
import CausalAlgebraicGeometry.NearVacuumGeneral

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CausalAlgebraicGeometry.NearVacuumStabilizationGeneral

open CausalAlgebraicGeometry.NearVacuumGeneral

/-! ## Embedding Fin(k+1) into Fin m -/

/-- The natural embedding Fin(k+1) → Fin m when k < m. -/
def embedFin {m k : ℕ} (hkm : k < m) (i : Fin (k + 1)) : Fin m :=
  ⟨i.val, by have := i.isLt; omega⟩

theorem embedFin_mono {m k : ℕ} (hkm : k < m) : Monotone (embedFin hkm) := by
  intro i j hij
  exact Fin.mk_le_mk.mpr (Fin.le_def.mp hij)

theorem embedFin_injective {m k : ℕ} (hkm : k < m) :
    Function.Injective (embedFin hkm) := by
  intro i j h
  apply Fin.ext
  have : (embedFin hkm i).val = (embedFin hkm j).val := congrArg Fin.val h
  unfold embedFin at this
  exact this

/-- Coordinate-wise embedding (Fin d → Fin(k+1)) → (Fin d → Fin m). -/
def embedPt {d m k : ℕ} (hkm : k < m) (p : Fin d → Fin (k + 1)) :
    Fin d → Fin m :=
  fun i => embedFin hkm (p i)

theorem embedPt_mono {d m k : ℕ} (hkm : k < m) :
    Monotone (embedPt (d := d) hkm) := by
  intro p q hpq i
  exact embedFin_mono hkm (hpq i)

theorem embedPt_injective {d m k : ℕ} (hkm : k < m) :
    Function.Injective (embedPt (d := d) hkm) := by
  intro p q h
  funext i
  have hi : embedPt hkm p i = embedPt hkm q i := congr_fun h i
  unfold embedPt at hi
  exact embedFin_injective hkm hi

/-- The image of embedPt consists exactly of points in [m]^d whose coordinates
    are all < k + 1. -/
theorem embedPt_image_iff {d m k : ℕ} (hkm : k < m) (p : Fin d → Fin m) :
    (∃ q : Fin d → Fin (k + 1), embedPt hkm q = p) ↔ (∀ i, (p i).val < k + 1) := by
  constructor
  · rintro ⟨q, rfl⟩ i
    unfold embedPt embedFin
    exact (q i).isLt
  · intro hp
    refine ⟨fun i => ⟨(p i).val, hp i⟩, ?_⟩
    funext i
    unfold embedPt embedFin
    exact Fin.ext rfl

/-! ## Restriction preserves antitone -/

/-- Restrict an antitone f : [m]^d → ℕ to [k+1]^d via embedding. -/
def restrictFn {d m k : ℕ} (hkm : k < m) (f : (Fin d → Fin m) → ℕ) :
    (Fin d → Fin (k + 1)) → ℕ :=
  fun p => f (embedPt hkm p)

theorem restrictFn_antitone {d m k : ℕ} (hkm : k < m) {f : (Fin d → Fin m) → ℕ}
    (hf : ∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → f q ≤ f p) :
    ∀ p q : Fin d → Fin (k + 1), (∀ i, p i ≤ q i) →
      restrictFn hkm f q ≤ restrictFn hkm f p := by
  intro p q hpq
  unfold restrictFn
  apply hf
  intro i
  exact embedFin_mono hkm (hpq i)

/-! ## Key identity: restriction + zero-at-boundary → sum preserved -/

/-- **SUM PRESERVATION**: For antitone f on [m]^d summing to k < m, the sum
    of its restriction to [k+1]^d equals k.

    This follows from zero-at-boundary: f vanishes outside [k+1]^d, so the
    total sum equals the sum over [k+1]^d, which equals the sum of restrictFn. -/
theorem restrictFn_sum_eq {d m k : ℕ} (hkm : k < m)
    {f : (Fin d → Fin m) → ℕ}
    (hf_anti : ∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → f q ≤ f p)
    (hf_sum : Finset.univ.sum f = k) :
    Finset.univ.sum (restrictFn hkm f) = k := by
  unfold restrictFn
  -- Goal: ∑ p : Fin d → Fin (k+1), f (embedPt hkm p) = k
  -- Step 1: rewrite as sum over image of embedPt via Finset.sum_image.
  have h_image : Finset.univ.sum (fun p : Fin d → Fin (k + 1) => f (embedPt hkm p)) =
                 (Finset.univ.image (embedPt hkm (d := d))).sum f := by
    symm
    apply Finset.sum_image
    intro q₁ _ q₂ _ h
    exact embedPt_injective hkm h
  rw [h_image]
  -- Step 2: sum over image = sum over universe since outside-image is zero.
  have h_outside_zero : ∀ p ∈ (Finset.univ \ Finset.univ.image (embedPt hkm (d := d))),
      f p = 0 := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    -- p ∉ image ⟹ ¬ (∀ i, (p i).val < k+1) ⟹ ∃ i with (p i).val ≥ k+1 > k
    have h_not_in : ¬ ∀ i, (p i).val < k + 1 := by
      intro h
      obtain ⟨q, hq⟩ := (embedPt_image_iff hkm p).mpr h
      exact hp.2 (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩)
    push_neg at h_not_in
    obtain ⟨i, hi⟩ := h_not_in
    exact antitone_zero_at_boundary_general hkm f hf_anti hf_sum p i (by omega)
  have h_eq_univ : (Finset.univ.image (embedPt hkm (d := d))).sum f = Finset.univ.sum f := by
    rw [show Finset.univ = Finset.univ.image (embedPt hkm (d := d)) ∪
            (Finset.univ \ Finset.univ.image (embedPt hkm (d := d))) from
          (Finset.union_sdiff_of_subset (Finset.subset_univ _)).symm,
        Finset.sum_union Finset.disjoint_sdiff]
    rw [Finset.sum_eq_zero h_outside_zero, add_zero]
  rw [h_eq_univ, hf_sum]

/-! ## Zero-extension: the inverse direction -/

/-- Extend g : [k+1]^d → ℕ to [m]^d by zero outside the subbox. -/
noncomputable def extendFn {d m k : ℕ} (hkm : k < m)
    (g : (Fin d → Fin (k + 1)) → ℕ) : (Fin d → Fin m) → ℕ :=
  fun p =>
    if h : ∀ i, (p i).val < k + 1 then
      g (fun i => ⟨(p i).val, h i⟩)
    else 0

/-- On the image of embedPt (points with coords < k+1), extendFn retrieves g. -/
theorem extendFn_eq_on_image {d m k : ℕ} (hkm : k < m)
    (g : (Fin d → Fin (k + 1)) → ℕ) (q : Fin d → Fin (k + 1)) :
    extendFn hkm g (embedPt hkm q) = g q := by
  unfold extendFn embedPt embedFin
  have h : ∀ i, ((⟨(q i).val, by have := (q i).isLt; omega⟩ : Fin m) : Fin m).val < k + 1 := by
    intro i; exact (q i).isLt
  rw [dif_pos h]

/-- Off the subbox, extendFn is zero. -/
theorem extendFn_zero_off_subbox {d m k : ℕ} (hkm : k < m)
    (g : (Fin d → Fin (k + 1)) → ℕ) (p : Fin d → Fin m)
    (hp : ¬ ∀ i, (p i).val < k + 1) :
    extendFn hkm g p = 0 := by
  unfold extendFn
  rw [dif_neg hp]

/-- Zero-extension preserves antitone.

    Proof: For p ≤ q componentwise, there are four cases based on whether p, q
    are in the subbox. Antitone is preserved in each case. -/
theorem extendFn_antitone {d m k : ℕ} (hkm : k < m)
    {g : (Fin d → Fin (k + 1)) → ℕ}
    (hg : ∀ p q : Fin d → Fin (k + 1), (∀ i, p i ≤ q i) → g q ≤ g p) :
    ∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → extendFn hkm g q ≤ extendFn hkm g p := by
  intro p q hpq
  by_cases hq : ∀ i, (q i).val < k + 1
  · -- q in subbox; then p also in subbox (since p ≤ q)
    have hp : ∀ i, (p i).val < k + 1 := by
      intro i
      have := Fin.le_def.mp (hpq i)
      have := hq i
      omega
    unfold extendFn
    rw [dif_pos hp, dif_pos hq]
    apply hg
    intro i
    exact Fin.mk_le_mk.mpr (Fin.le_def.mp (hpq i))
  · -- q outside subbox: extendFn q = 0 ≤ extendFn p
    rw [extendFn_zero_off_subbox hkm g q hq]
    omega

/-- Zero-extension preserves the sum. -/
theorem extendFn_sum {d m k : ℕ} (hkm : k < m)
    (g : (Fin d → Fin (k + 1)) → ℕ) :
    Finset.univ.sum (extendFn hkm g) = Finset.univ.sum g := by
  -- Strategy: sum over univ = sum over image of embedPt + sum over complement.
  -- Image contributes: sum over [k+1]^d of g (via bijection).
  -- Complement contributes: 0 (by extendFn_zero_off_subbox).
  -- Then: sum = sum g + 0 = sum g.
  let img : Finset (Fin d → Fin m) := Finset.univ.image (embedPt hkm (d := d))
  have h_univ_eq : (Finset.univ : Finset (Fin d → Fin m)) = img ∪ (Finset.univ \ img) :=
    (Finset.union_sdiff_of_subset (Finset.subset_univ _)).symm
  have h_disj : Disjoint img (Finset.univ \ img) := Finset.disjoint_sdiff
  have h_comp_zero : (Finset.univ \ img).sum (extendFn hkm g) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_sdiff] at hp
    have h_not : ¬ ∀ i, (p i).val < k + 1 := by
      intro h
      obtain ⟨q, hq⟩ := (embedPt_image_iff hkm p).mpr h
      exact hp.2 (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩)
    exact extendFn_zero_off_subbox hkm g p h_not
  have h_img_eq_sum_g : img.sum (extendFn hkm g) = Finset.univ.sum g := by
    show (Finset.univ.image (embedPt hkm (d := d))).sum (extendFn hkm g) = Finset.univ.sum g
    rw [Finset.sum_image (fun q₁ _ q₂ _ h => embedPt_injective hkm h)]
    apply Finset.sum_congr rfl
    intro q _
    exact extendFn_eq_on_image hkm g q
  calc Finset.univ.sum (extendFn hkm g)
      = (img ∪ (Finset.univ \ img)).sum (extendFn hkm g) := by rw [← h_univ_eq]
    _ = img.sum (extendFn hkm g) + (Finset.univ \ img).sum (extendFn hkm g) :=
        Finset.sum_union h_disj
    _ = Finset.univ.sum g + 0 := by rw [h_img_eq_sum_g, h_comp_zero]
    _ = Finset.univ.sum g := by omega

/-- Zero-extension gives an antitone function summing to k when g is. -/
theorem extendFn_preserves_constraints {d m k : ℕ} (hkm : k < m)
    {g : (Fin d → Fin (k + 1)) → ℕ}
    (hg_anti : ∀ p q : Fin d → Fin (k + 1), (∀ i, p i ≤ q i) → g q ≤ g p)
    (hg_sum : Finset.univ.sum g = k) :
    (∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) →
       extendFn hkm g q ≤ extendFn hkm g p) ∧
    Finset.univ.sum (extendFn hkm g) = k := by
  refine ⟨extendFn_antitone hkm hg_anti, ?_⟩
  rw [extendFn_sum hkm g, hg_sum]

/-! ## The mutual inverse property -/

/-- Restriction of extension = identity on [k+1]^d. -/
theorem restrict_extend {d m k : ℕ} (hkm : k < m)
    (g : (Fin d → Fin (k + 1)) → ℕ) :
    restrictFn hkm (extendFn hkm g) = g := by
  funext p
  unfold restrictFn
  exact extendFn_eq_on_image hkm g p

/-- Extension of restriction = original function, given zero-at-boundary.

    For antitone f : [m]^d → ℕ summing to k < m, f vanishes outside [k+1]^d.
    So extendFn (restrictFn f) = f everywhere. -/
theorem extend_restrict {d m k : ℕ} (hkm : k < m)
    {f : (Fin d → Fin m) → ℕ}
    (hf_anti : ∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → f q ≤ f p)
    (hf_sum : Finset.univ.sum f = k) :
    extendFn hkm (restrictFn hkm f) = f := by
  funext p
  by_cases hp : ∀ i, (p i).val < k + 1
  · -- p in subbox: extendFn (restrictFn f) p = f (embedPt (restrict p)) = f p
    unfold extendFn
    rw [dif_pos hp]
    unfold restrictFn embedPt embedFin
    congr 1
  · -- p outside subbox: extendFn = 0, and f p = 0 by zero-at-boundary
    rw [extendFn_zero_off_subbox hkm _ p hp]
    push_neg at hp
    obtain ⟨i, hi⟩ := hp
    exact (antitone_zero_at_boundary_general hkm f hf_anti hf_sum p i (by omega)).symm

/-! ## The Equiv packaging: cardinality equality -/

/-- The type of antitone functions [m]^d → ℕ summing to k. -/
def AntitoneSum (d m k : ℕ) : Type :=
  { f : (Fin d → Fin m) → ℕ //
    (∀ p q : Fin d → Fin m, (∀ i, p i ≤ q i) → f q ≤ f p) ∧
    Finset.univ.sum f = k }

/-- **PACKAGED BIJECTION**: For m > k, the map f ↦ restrictFn f is a bijection
    AntitoneSum d m k ≃ AntitoneSum d (k+1) k. -/
noncomputable def antitoneSum_stabilize_equiv {d m k : ℕ} (hkm : k < m) :
    AntitoneSum d m k ≃ AntitoneSum d (k + 1) k where
  toFun f := ⟨restrictFn hkm f.val,
    restrictFn_antitone hkm f.property.1,
    restrictFn_sum_eq hkm f.property.1 f.property.2⟩
  invFun g := ⟨extendFn hkm g.val,
    extendFn_antitone hkm g.property.1,
    (extendFn_preserves_constraints hkm g.property.1 g.property.2).2⟩
  left_inv f := by
    apply Subtype.ext
    exact extend_restrict hkm f.property.1 f.property.2
  right_inv g := by
    apply Subtype.ext
    exact restrict_extend hkm g.val

/-! ## Summary

PROVED (zero sorry):

1. embedFin / embedPt: monotone injective embeddings [k+1] ↪ [m] and [k+1]^d ↪ [m]^d.
2. embedPt_image_iff: image of embedPt equals "coordinate < k+1" subset.
3. restrictFn_antitone: restriction preserves antitone.
4. restrictFn_sum_eq: restriction preserves the k total (via zero-at-boundary).

STRUCTURAL CONSEQUENCE:
  For m > k, restriction f ↦ restrictFn hkm f is a well-defined map from
    {antitone f : [m]^d → ℕ : Σf = k}  →  {antitone g : [k+1]^d → ℕ : Σg = k}
  This map is injective (by embedPt_injective + zero-at-boundary uniquely
  determines f from its restriction).

  The inverse map is zero-extension, mapping antitone g on [k+1]^d to the
  antitone f on [m]^d that equals g on the subbox and 0 elsewhere.

  Together: the count is independent of m for m > k. The d=1 case
  (NearVacuumFull.nonIncSeqCount_stable) is a special case.

  This generalizes the d=1 stabilization to arbitrary dimension d.

FOR FULL BIJECTION (Equiv between subtypes):
  The remaining step is packaging restrictFn and extendFn as an Equiv between
  the subtypes {f : (Fin d → Fin m) → ℕ // antitone ∧ sum=k} and the analog
  for [k+1]^d. The theorems above provide all the ingredients. The packaging
  is a routine Lean Equiv construction.
-/

end CausalAlgebraicGeometry.NearVacuumStabilizationGeneral
