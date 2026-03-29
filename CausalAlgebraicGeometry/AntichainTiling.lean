/-
  AntichainTiling.lean — Antichain-based tiling for the full dimension law

  Key result: For d ≥ 2, embed A(k,d) pairwise-incomparable copies of [m]^d
  into [km]^d, where A(k,d) is the max antichain size of [k]^d ≈ k^{d-1}.
  This gives: |CC([km]^d)| ≥ |CC([m]^d)|^{A(k,d)}.
-/
import CausalAlgebraicGeometry.DimensionLaw

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace CausalAlgebraicGeometry.AntichainTiling

open CausalAlgebraicGeometry.DimensionLaw

open scoped Classical
noncomputable section

/-- Embed [m]^d into [km]^d at offset α ∈ [k]^d. -/
def blockEmbed (d m k : ℕ) (α : Fin d → Fin k) (f : Fin d → Fin m) :
    Fin d → Fin (k * m) :=
  fun i => ⟨(α i).val * m + (f i).val, by
    have := (α i).isLt; have := (f i).isLt; nlinarith⟩

theorem blockEmbed_injective (d m k : ℕ) (α : Fin d → Fin k) :
    Function.Injective (blockEmbed d m k α) := by
  intro f g h; funext i
  have hi := congr_fun h i
  simp only [blockEmbed, Fin.mk.injEq] at hi; ext; omega

theorem blockEmbed_preserves_le (d m k : ℕ) (α : Fin d → Fin k)
    (f g : Fin d → Fin m) :
    f ≤ g ↔ blockEmbed d m k α f ≤ blockEmbed d m k α g := by
  simp only [Pi.le_def, Fin.le_def, blockEmbed]
  constructor <;> intro h i <;> have := h i <;> omega

theorem blockEmbed_preserves_convex (d m k : ℕ) (α : Fin d → Fin k)
    (S : Finset (Fin d → Fin m)) (hS : IsConvexDim d m S) :
    IsConvexDim d (k * m) (S.image (blockEmbed d m k α)) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_image] at ha hb ⊢
  obtain ⟨a', ha'S, rfl⟩ := ha
  obtain ⟨b', hb'S, rfl⟩ := hb
  have hab' : a' ≤ b' := (blockEmbed_preserves_le d m k α a' b').mpr hab
  have hc_lo : ∀ i, (α i).val * m + (a' i).val ≤ (c i).val :=
    fun i => Fin.le_def.mp ((Pi.le_def.mp hac) i)
  have hc_hi : ∀ i, (c i).val ≤ (α i).val * m + (b' i).val :=
    fun i => Fin.le_def.mp ((Pi.le_def.mp hcb) i)
  let c' : Fin d → Fin m := fun i =>
    ⟨(c i).val - (α i).val * m, by have := hc_lo i; have := hc_hi i; have := (b' i).isLt; omega⟩
  refine ⟨c', ?_, ?_⟩
  · apply hS a' ha'S b' hb'S hab' c'
    · intro i; show (a' i).val ≤ (c' i).val; simp only [c']; have := hc_lo i; omega
    · intro i; show (c' i).val ≤ (b' i).val; simp only [c']; have := hc_hi i; omega
  · funext i; show blockEmbed d m k α c' i = c i
    simp only [blockEmbed, c']; ext; simp only; have := hc_lo i; omega

/-- If a*m + f ≤ b*m + g and g < m, then a ≤ b. -/
private theorem le_of_blocked_embed_le (a b f g m : ℕ)
    (h : a * m + f ≤ b * m + g) (hg : g < m) : a ≤ b := by
  by_contra hab
  simp only [Nat.not_le] at hab
  -- hab : b < a, i.e., b + 1 ≤ a
  have h1 : (b + 1) * m ≤ a * m := Nat.mul_le_mul_right m hab
  -- h1 : b*m + m ≤ a*m
  -- So a*m + f ≥ b*m + m + f ≥ b*m + m > b*m + g = RHS
  have h2 : b * m + m ≤ a * m + f := Nat.le_add_right _ f |>.trans (by linarith) |> id
  -- Hmm linarith won't work. Use nlinarith.
  nlinarith [Nat.zero_le f]

/-- Points from incomparable blocks are incomparable. -/
theorem block_incomparable (d m k : ℕ) (hm : 0 < m)
    (α β : Fin d → Fin k) (h1 : ¬(α ≤ β)) (_ : ¬(β ≤ α))
    (f g : Fin d → Fin m) :
    ¬(blockEmbed d m k α f ≤ blockEmbed d m k β g) := by
  intro h; apply h1; intro i; rw [Fin.le_def]
  -- (α i)*m + f(i) ≤ (β i)*m + g(i) → (α i) ≤ (β i)
  -- since f(i) < m and g(i) < m.
  exact le_of_blocked_embed_le (α i).val (β i).val (f i).val (g i).val m
    (Fin.le_def.mp ((Pi.le_def.mp h) i)) (g i).isLt

/-- Union of convex sets at antichain positions is convex. -/
theorem antichain_union_convex (d m k : ℕ) (hm : 0 < m)
    (ac : Finset (Fin d → Fin k))
    (h_anti : ∀ α ∈ ac, ∀ β ∈ ac, α ≠ β → ¬(α ≤ β))
    (choices : (Fin d → Fin k) → Finset (Fin d → Fin m))
    (h_convex : ∀ α ∈ ac, IsConvexDim d m (choices α)) :
    IsConvexDim d (k * m)
      (ac.biUnion (fun α => (choices α).image (blockEmbed d m k α))) := by
  intro a ha b hb hab c hac hcb
  rw [Finset.mem_biUnion] at ha hb ⊢
  obtain ⟨α, hα_mem, ha_img⟩ := ha
  obtain ⟨β, hβ_mem, hb_img⟩ := hb
  by_cases hαβ : α = β
  · subst hαβ
    exact ⟨α, hα_mem, blockEmbed_preserves_convex d m k α (choices α) (h_convex α hα_mem)
      a ha_img b hb_img hab c hac hcb⟩
  · exfalso
    rw [Finset.mem_image] at ha_img hb_img
    obtain ⟨f, _, rfl⟩ := ha_img
    obtain ⟨g, _, rfl⟩ := hb_img
    exact block_incomparable d m k hm α β (h_anti α hα_mem β hβ_mem hαβ)
      (h_anti β hβ_mem α hα_mem (Ne.symm hαβ)) f g hab

/-! ### The tiling inequality -/

/-- Given a dependent choice function from `ac.pi`, extract the choice for α
    using classical logic. -/
private noncomputable def piChoose {d m k : ℕ}
    (ac : Finset (Fin d → Fin k))
    (choices : ∀ a, a ∈ ac → Finset (Fin d → Fin m))
    (α : Fin d → Fin k) : Finset (Fin d → Fin m) :=
  if h : α ∈ ac then choices α h else ∅

/-- The tiling map: send a choice function to the union of embedded copies. -/
private noncomputable def tilingMap (d m k : ℕ)
    (ac : Finset (Fin d → Fin k))
    (choices : ∀ a, a ∈ ac → Finset (Fin d → Fin m)) :
    Finset (Fin d → Fin (k * m)) :=
  ac.biUnion (fun α => (piChoose ac choices α).image (blockEmbed d m k α))

private theorem piChoose_eq {d m k : ℕ}
    {ac : Finset (Fin d → Fin k)}
    {choices : ∀ a, a ∈ ac → Finset (Fin d → Fin m)}
    {α : Fin d → Fin k} (hα : α ∈ ac) :
    piChoose ac choices α = choices α hα := by
  simp [piChoose, hα]

/-- A point in block α has coordinates in [α(i)*m, (α(i)+1)*m - 1]. -/
private theorem blockEmbed_coord_range (d m k : ℕ) (α : Fin d → Fin k)
    (f : Fin d → Fin m) (i : Fin d) :
    (α i).val * m ≤ (blockEmbed d m k α f i).val ∧
    (blockEmbed d m k α f i).val < ((α i).val + 1) * m := by
  simp only [blockEmbed]
  constructor
  · omega
  · have := (f i).isLt; nlinarith

/-- Points from different blocks have different coordinate ranges. -/
private theorem blockEmbed_determines_block (d m k : ℕ) (hm : 0 < m)
    (α β : Fin d → Fin k) (f : Fin d → Fin m) (g : Fin d → Fin m)
    (h : blockEmbed d m k α f = blockEmbed d m k β g) : α = β := by
  funext i
  have hi := congr_fun h i
  simp only [blockEmbed, Fin.mk.injEq] at hi
  have hf := (f i).isLt
  have hg := (g i).isLt
  ext
  -- α(i)*m + f(i) = β(i)*m + g(i), f(i) < m, g(i) < m → α(i) = β(i)
  -- Use: a*m + f = b*m + g with f < m, g < m implies a = b
  have := le_of_blocked_embed_le (α i).val (β i).val (f i).val (g i).val m
    (by omega) hg
  have := le_of_blocked_embed_le (β i).val (α i).val (g i).val (f i).val m
    (by omega) hf
  omega

/-- Filtering the tiling image to recover a single block's contribution. -/
private theorem mem_tilingMap_of_block {d m k : ℕ} {hm : 0 < m}
    {ac : Finset (Fin d → Fin k)}
    {choices : ∀ a, a ∈ ac → Finset (Fin d → Fin m)}
    {α : Fin d → Fin k} (hα : α ∈ ac)
    {p : Fin d → Fin (k * m)}
    (hp : p ∈ (choices α hα).image (blockEmbed d m k α)) :
    p ∈ tilingMap d m k ac choices := by
  simp only [tilingMap]
  rw [Finset.mem_biUnion]
  exact ⟨α, hα, by rwa [piChoose_eq hα]⟩

theorem tiling_inequality (d m k : ℕ) (hm : 0 < m)
    (ac : Finset (Fin d → Fin k))
    (h_anti : ∀ α ∈ ac, ∀ β ∈ ac, α ≠ β → ¬(α ≤ β)) :
    numConvexDim d m ^ ac.card ≤ numConvexDim d (k * m) := by
  -- Rewrite in terms of cardinalities
  simp only [numConvexDim_eq_card]
  rw [show (convexSubsetsDim d m).card ^ ac.card =
    (ac.pi (fun _ => convexSubsetsDim d m)).card from by
    rw [Finset.card_pi]; exact (Finset.prod_const _).symm]
  -- Show the cardinality bound via injection
  apply Finset.card_le_card_of_injOn (tilingMap d m k ac)
  · -- The map lands in convexSubsetsDim d (k * m)
    intro choices hchoices
    simp only [Finset.mem_coe] at hchoices
    simp only [convexSubsetsDim, Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · exact Finset.subset_univ _
    · apply antichain_union_convex d m k hm ac h_anti (piChoose ac choices)
      intro α hα
      have hmem := Finset.mem_pi.mp hchoices α hα
      rw [convexSubsetsDim, Finset.mem_filter, Finset.mem_powerset] at hmem
      rw [piChoose_eq hα]; exact hmem.2
  · -- Injectivity
    intro f hf g hg hfg
    rw [Finset.mem_coe] at hf hg
    funext α hα
    -- The tiling maps are equal
    -- tilingMap f = tilingMap g means the biUnions are equal as Finsets
    -- For each α, the image of choices f α under blockEmbed α is disjoint
    -- from images of choices f β for β ≠ α
    -- So we can recover choices f α by filtering the tiling on block α
    -- Show: the embedded image at α can be recovered by filtering
    ext p
    constructor
    · intro hp
      -- p ∈ f α hα, so blockEmbed α p ∈ tilingMap f = tilingMap g
      have hp_in : blockEmbed d m k α p ∈ tilingMap d m k ac f := by
        simp only [tilingMap, Finset.mem_biUnion]
        exact ⟨α, hα, by rw [piChoose_eq hα]; exact Finset.mem_image_of_mem _ hp⟩
      rw [hfg] at hp_in
      simp only [tilingMap, Finset.mem_biUnion] at hp_in
      obtain ⟨β, hβ, hp_β⟩ := hp_in
      rw [piChoose_eq hβ, Finset.mem_image] at hp_β
      obtain ⟨q, hq_mem, hq_eq⟩ := hp_β
      have hαβ : α = β := blockEmbed_determines_block d m k hm α β p q hq_eq.symm
      subst hαβ
      have : p = q := blockEmbed_injective d m k α hq_eq.symm
      rwa [this]
    · intro hp
      -- p ∈ g α hα, so blockEmbed α p ∈ tilingMap g = tilingMap f
      have hp_in : blockEmbed d m k α p ∈ tilingMap d m k ac g := by
        simp only [tilingMap, Finset.mem_biUnion]
        exact ⟨α, hα, by rw [piChoose_eq hα]; exact Finset.mem_image_of_mem _ hp⟩
      rw [← hfg] at hp_in
      simp only [tilingMap, Finset.mem_biUnion] at hp_in
      obtain ⟨β, hβ, hp_β⟩ := hp_in
      rw [piChoose_eq hβ, Finset.mem_image] at hp_β
      obtain ⟨q, hq_mem, hq_eq⟩ := hp_β
      have hαβ : α = β := blockEmbed_determines_block d m k hm α β p q hq_eq.symm
      subst hαβ
      have : p = q := blockEmbed_injective d m k α hq_eq.symm
      rwa [this]

end -- section
end CausalAlgebraicGeometry.AntichainTiling
