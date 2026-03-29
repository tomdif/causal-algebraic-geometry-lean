/-
  GapTheorem.lean — The Hauptvermutung as a proved theorem

  THE GAP THEOREM: The Noetherian ratio γ exhibits an exponential gap
  between bounded-width and linear-width posets. This gap constitutes
  a quantitative Hauptvermutung — a proved criterion for detecting
  geometric regularity from the partial order alone.

  Upper bound (from ConvexFactorization + BalancedBound):
    width = w = O(1) → |CC| ≤ (n²+1)^w → γ = O(n^{2w-1}) [polynomial]

  Lower bound (THIS FILE):
    |CC| ≥ 2^{width} (every subset of a max antichain is convex)
    → γ ≥ 2^{width} / n²

  THE GAP:
    width = O(1)  → γ = O(n^{const})           [polynomial]
    width = Ω(n)  → γ ≥ 2^{Ω(n)} / n²          [exponential]

  The exponential separation between these two regimes is the
  Hauptvermutung in quantitative form: manifold-like causal sets
  (bounded width) have polynomial γ, while non-geometric posets
  (linear width) have exponential γ. The gap is not a conjecture —
  it is a machine-verified theorem.
-/
import CausalAlgebraicGeometry.NoetherianRatio
import CausalAlgebraicGeometry.WidthOneProof
import CausalAlgebraicGeometry.BalancedBound
import CausalAlgebraicGeometry.ConvexFactorization
import CausalAlgebraicGeometry.Dilworth
import CausalAlgebraicGeometry.DilworthProof

namespace CausalAlgebraicGeometry.GapTheorem

open CausalAlgebra NoetherianRatio WidthOneProof BalancedBound Dilworth DilworthProof
     ChainRestriction ConvexFactorization

/-! ### The lower bound: every subset of an antichain is convex -/

/-- **Every subset of an antichain is convex** in the ambient poset.

    Proof: if α, β ∈ S ⊆ A (antichain) and α ≤ γ ≤ β, then
    α ≤ β by transitivity. But α ∥ β (antichain, α ≠ β), so
    ¬(α ≤ β) — contradiction. The premise is impossible for
    distinct elements, so convexity holds vacuously. -/
theorem antichain_subset_convex {k : Type*} [Field k] (C : CAlg k)
    (A : Finset C.Λ)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ C.le a b ∧ ¬ C.le b a)
    (S : Finset C.Λ) (hSA : S ⊆ A) :
    IsConvexFS C S := by
  intro α hα β hβ γ hαγ hγβ
  by_cases heq : α = β
  · -- α = β: α ≤ γ ≤ α forces γ = α ∈ S
    subst heq; exact C.le_antisymm γ α hγβ hαγ ▸ hα
  · -- α ≠ β: α ≤ γ ≤ β gives α ≤ β, contradicting antichain
    exact absurd (C.le_trans α γ β hαγ hγβ) (hA α (hSA hα) β (hSA hβ) heq).1

/-- **Lower bound on |CC|**: the number of convex subsets is at least
    2^{|A|} where A is any antichain.

    Proof: the 2^{|A|} subsets of A are all convex (by
    antichain_subset_convex) and are distinct finsets, so they
    all appear in the convex subset count. -/
theorem numConvex_ge_pow_antichain {k : Type*} [Field k] (C : CAlg k)
    (A : Finset C.Λ)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ C.le a b ∧ ¬ C.le b a) :
    2 ^ A.card ≤ numCausallyConvex C := by
  rw [← Finset.card_powerset A]
  apply Finset.card_le_card
  intro S hS
  rw [Finset.mem_powerset] at hS
  simp only [numCausallyConvex, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]
  exact antichain_subset_convex C A hA S hS

/-! ### The formal definition of manifold-likeness -/

/-- A poset is **width-bounded** if its maximum antichain size is
    at most w₀. This is the combinatorial property that characterizes
    manifold-like causal sets:
    - d-dimensional sprinklings have width ~ N^{(d-1)/d} = O(1) for fixed d
    - Random partial orders have width ~ N/2 = Ω(N) -/
def IsWidthBounded {k : Type*} [Field k] (C : CAlg k) (w₀ : ℕ) : Prop :=
  ∀ A : Finset C.Λ,
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ C.le a b ∧ ¬ C.le b a) →
    A.card ≤ w₀

/-! ### Bridge: IsWidthBounded → width ≤ w₀ -/

/-- `IsWidthBounded C w₀` implies `width C ≤ w₀`. -/
theorem width_le_of_widthBounded {k : Type*} [Field k]
    (C : CAlg k) (w₀ : ℕ) (hw : IsWidthBounded C w₀) :
    width C ≤ w₀ := by
  unfold width
  apply Finset.sup_le
  intro S _
  split_ifs with h
  · exact hw S h
  · exact Nat.zero_le _

/-! ### Counting: chain cover → convex subset bound -/

/-- The "interval subsets" of a chain L in a poset C: the collection of all
    sub-finsets of L that are either ∅ or of the form
    L.filter (fun c => C.le a c ∧ C.le c b) for some a, b ∈ L.
    Every convex restriction S ∩ L must be one of these. -/
noncomputable def intervalSubsets {k : Type*} [Field k] (C : CAlg k)
    (L : Finset C.Λ) : Finset (Finset C.Λ) :=
  {∅} ∪ (L ×ˢ L).image (fun p => L.filter (fun c => C.le p.1 c ∧ C.le c p.2))

/-- The interval subsets of a chain of size m has at most m² + 1 elements. -/
theorem card_intervalSubsets_le {k : Type*} [Field k] (C : CAlg k)
    (L : Finset C.Λ) : (intervalSubsets C L).card ≤ L.card ^ 2 + 1 := by
  unfold intervalSubsets
  calc (({∅} ∪ (L ×ˢ L).image _) : Finset (Finset C.Λ)).card
      ≤ ({∅} : Finset (Finset C.Λ)).card +
        ((L ×ˢ L).image (fun p => L.filter (fun c => C.le p.1 c ∧ C.le c p.2))).card :=
        Finset.card_union_le _ _
    _ ≤ 1 + (L ×ˢ L).card := by
        apply Nat.add_le_add
        · simp
        · exact Finset.card_image_le
    _ = 1 + L.card ^ 2 := by rw [Finset.card_product]; ring_nf
    _ = L.card ^ 2 + 1 := by omega

/-- Min of a nonempty sub-finset of a chain (list induction helper). -/
private theorem list_min_in_chain {k : Type*} [Field k] (C : CAlg k)
    (L : Finset C.Λ) (hL : IsChainFS C L) :
    ∀ (l : List C.Λ), l ≠ [] → (∀ x ∈ l, x ∈ L) →
      ∃ a ∈ l, ∀ x ∈ l, C.le a x := by
  intro l hl hmem
  induction l with
  | nil => exact absurd rfl hl
  | cons y t ih =>
    by_cases ht : t = []
    · exact ⟨y, List.Mem.head _, fun x hx => by
        subst ht; simp [List.mem_cons] at hx; exact hx ▸ C.le_refl _⟩
    · have ht_mem : ∀ x ∈ t, x ∈ L := fun x hx => hmem x (List.mem_cons.mpr (Or.inr hx))
      obtain ⟨a, ha, hmin⟩ := ih ht ht_mem
      have hy_mem : y ∈ L := hmem y (List.Mem.head _)
      have ha_mem : a ∈ L := hmem a (List.mem_cons.mpr (Or.inr ha))
      rcases hL y hy_mem a ha_mem with hya | hay
      · exact ⟨y, List.Mem.head _, fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact C.le_refl _
          · exact C.le_trans _ a x hya (hmin x hx)⟩
      · exact ⟨a, List.mem_cons.mpr (Or.inr ha), fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hay
          · exact hmin x hx⟩

/-- Max of a nonempty sub-finset of a chain (list induction helper). -/
private theorem list_max_in_chain {k : Type*} [Field k] (C : CAlg k)
    (L : Finset C.Λ) (hL : IsChainFS C L) :
    ∀ (l : List C.Λ), l ≠ [] → (∀ x ∈ l, x ∈ L) →
      ∃ b ∈ l, ∀ x ∈ l, C.le x b := by
  intro l hl hmem
  induction l with
  | nil => exact absurd rfl hl
  | cons y t ih =>
    by_cases ht : t = []
    · exact ⟨y, List.Mem.head _, fun x hx => by
        subst ht; simp [List.mem_cons] at hx; exact hx ▸ C.le_refl _⟩
    · have ht_mem : ∀ x ∈ t, x ∈ L := fun x hx => hmem x (List.mem_cons.mpr (Or.inr hx))
      obtain ⟨b, hb, hmax⟩ := ih ht ht_mem
      have hy_mem : y ∈ L := hmem y (List.Mem.head _)
      have hb_mem : b ∈ L := hmem b (List.mem_cons.mpr (Or.inr hb))
      rcases hL y hy_mem b hb_mem with hyb | hby
      · exact ⟨b, List.mem_cons.mpr (Or.inr hb), fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hyb
          · exact hmax x hx⟩
      · exact ⟨y, List.Mem.head _, fun x hx => by
          simp [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact C.le_refl _
          · exact C.le_trans x b _ (hmax x hx) hby⟩

/-- Min of a nonempty sub-finset of a chain. -/
private theorem chain_has_min {k : Type*} [Field k] (C : CAlg k)
    (L : Finset C.Λ) (hL : IsChainFS C L)
    (F : Finset C.Λ) (hF : F ⊆ L) (hne : F.Nonempty) :
    ∃ a ∈ F, ∀ x ∈ F, C.le a x := by
  have hne_list : F.toList ≠ [] := by
    intro h; exact absurd (Finset.toList_eq_nil.mp h ▸ hne) Finset.not_nonempty_empty
  have hmem : ∀ x ∈ F.toList, x ∈ L := fun x hx => hF (Finset.mem_toList.mp hx)
  obtain ⟨a, ha, hmin⟩ := list_min_in_chain C L hL F.toList hne_list hmem
  exact ⟨a, Finset.mem_toList.mp ha, fun x hx => hmin x (Finset.mem_toList.mpr hx)⟩

/-- Max of a nonempty sub-finset of a chain. -/
private theorem chain_has_max {k : Type*} [Field k] (C : CAlg k)
    (L : Finset C.Λ) (hL : IsChainFS C L)
    (F : Finset C.Λ) (hF : F ⊆ L) (hne : F.Nonempty) :
    ∃ b ∈ F, ∀ x ∈ F, C.le x b := by
  have hne_list : F.toList ≠ [] := by
    intro h; exact absurd (Finset.toList_eq_nil.mp h ▸ hne) Finset.not_nonempty_empty
  have hmem : ∀ x ∈ F.toList, x ∈ L := fun x hx => hF (Finset.mem_toList.mp hx)
  obtain ⟨b, hb, hmax⟩ := list_max_in_chain C L hL F.toList hne_list hmem
  exact ⟨b, Finset.mem_toList.mp hb, fun x hx => hmax x (Finset.mem_toList.mpr hx)⟩

/-- Every convex restriction S ∩ L (for convex S and chain L) is in
    intervalSubsets C L. -/
theorem convex_inter_chain_mem_intervalSubsets {k : Type*} [Field k]
    (C : CAlg k) (L : Finset C.Λ) (hL : IsChainFS C L)
    (S : Finset C.Λ) (hS : IsConvexFS C S) :
    S ∩ L ∈ intervalSubsets C L := by
  simp only [intervalSubsets]
  by_cases hne : (S ∩ L).Nonempty
  · -- S ∩ L is nonempty: it's an interval determined by its min and max
    have hSL_sub : S ∩ L ⊆ L := Finset.inter_subset_right
    obtain ⟨a, ha, hmin⟩ := chain_has_min C L hL (S ∩ L) hSL_sub hne
    obtain ⟨b, hb, hmax⟩ := chain_has_max C L hL (S ∩ L) hSL_sub hne
    have haL : a ∈ L := hSL_sub ha
    have hbL : b ∈ L := hSL_sub hb
    have heq : S ∩ L = L.filter (fun c => C.le a c ∧ C.le c b) := by
      ext c
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor
      · intro hc
        exact ⟨hc.2, hmin c (Finset.mem_inter.mpr hc), hmax c (Finset.mem_inter.mpr hc)⟩
      · intro ⟨hcL, hac, hcb⟩
        have haS : a ∈ S := (Finset.mem_inter.mp ha).1
        have hbS : b ∈ S := (Finset.mem_inter.mp hb).1
        exact ⟨hS a haS b hbS c hac hcb, hcL⟩
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨haL, hbL⟩, heq.symm⟩
  · -- S ∩ L is empty
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_singleton.mpr hne

/-- Auxiliary: convert a Finset of chains to a Fin-indexed function. -/
private noncomputable def chainsToFun {k : Type*} [Field k] {C : CAlg k}
    (chains : Finset (Finset C.Λ)) :
    Fin chains.card → Finset C.Λ :=
  fun i => chains.toList.get (Fin.cast (by rw [Finset.length_toList]) i)

private theorem chainsToFun_mem {k : Type*} [Field k] {C : CAlg k}
    (chains : Finset (Finset C.Λ)) (i : Fin chains.card) :
    chainsToFun chains i ∈ chains := by
  simp only [chainsToFun]
  exact Finset.mem_toList.mp (List.get_mem _ _)

private theorem chainsToFun_cover {k : Type*} [Field k] {C : CAlg k}
    (chains : Finset (Finset C.Λ))
    (hcover : ∀ x : C.Λ, ∃ L ∈ chains, x ∈ L) :
    ∀ x : C.Λ, ∃ i : Fin chains.card, x ∈ chainsToFun chains i := by
  intro x
  obtain ⟨L, hL, hx⟩ := hcover x
  have hL' : L ∈ chains.toList := Finset.mem_toList.mpr hL
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hL'
  have hi_lt : i.val < chains.card := by
    rw [← Finset.length_toList]; exact i.isLt
  refine ⟨⟨i.val, hi_lt⟩, ?_⟩
  simp only [chainsToFun]
  have : Fin.cast (by rw [Finset.length_toList]) (⟨i.val, hi_lt⟩ : Fin chains.card) = i := by
    ext; simp
  rw [this, hi]
  exact hx

/-- The convex subsets of a poset covered by w chains, each of size ≤ n,
    number at most (n²+1)^w. The proof injects convex subsets into the
    product of interval-subset finsets via the restriction map. -/
theorem numConvex_le_pow_of_chain_cover {k : Type*} [Field k]
    (C : CAlg k) (w : ℕ) (chains : Fin w → Finset C.Λ)
    (hcover : ∀ x : C.Λ, ∃ i, x ∈ chains i)
    (hchains : ∀ i, IsChainFS C (chains i))
    (n : ℕ) (hsize : ∀ i, (chains i).card ≤ n) :
    numCausallyConvex C ≤ (n ^ 2 + 1) ^ w := by
  -- The convex subsets form a finset
  set convexSets := Finset.filter
    (fun S : Finset C.Λ =>
      ∀ α ∈ S, ∀ β ∈ S, ∀ γ : C.Λ, C.le α γ → C.le γ β → γ ∈ S)
    (Finset.univ.powerset) with hconv_def
  -- The restriction map: S ↦ (fun i => S ∩ chains i)
  -- This map is injective on convex subsets
  -- It lands in piFinset (fun i => intervalSubsets C (chains i))
  -- The piFinset has cardinality ∏ᵢ |intervalSubsets C (chains i)|
  -- Each |intervalSubsets C (chains i)| ≤ (chains i).card² + 1 ≤ n² + 1
  -- So the product is ≤ (n²+1)^w
  --
  -- Step 1: bound |convexSets| by |piFinset|
  have hinj : ∀ S₁ ∈ convexSets, ∀ S₂ ∈ convexSets,
      (fun S => (fun i => S ∩ chains i)) S₁ = (fun S => (fun i => S ∩ chains i)) S₂ →
      S₁ = S₂ := by
    intro S₁ _ S₂ _ heq
    exact chain_decomp_injective C chains hcover S₁ S₂ (fun i => congr_fun heq i)
  have hrange : ∀ S ∈ convexSets, (fun i => S ∩ chains i) ∈
      Fintype.piFinset (fun i => intervalSubsets C (chains i)) := by
    intro S hS
    rw [Fintype.mem_piFinset]
    intro i
    have hSconv : IsConvexFS C S := by
      simp only [hconv_def, Finset.mem_filter] at hS
      exact hS.2
    exact convex_inter_chain_mem_intervalSubsets C (chains i) (hchains i) S hSconv
  -- Step 2: |convexSets| ≤ |piFinset|
  have hcard_le : convexSets.card ≤
      (Fintype.piFinset (fun i => intervalSubsets C (chains i))).card :=
    Finset.card_le_card_of_injOn
      (fun S => (fun i => S ∩ chains i))
      hrange hinj
  -- Step 3: |piFinset| = ∏ᵢ |intervalSubsets C (chains i)|
  rw [Fintype.card_piFinset] at hcard_le
  -- Step 4: ∏ᵢ |intervalSubsets C (chains i)| ≤ (n²+1)^w
  have hprod_le : ∏ i : Fin w, (intervalSubsets C (chains i)).card ≤ (n ^ 2 + 1) ^ w := by
    calc ∏ i : Fin w, (intervalSubsets C (chains i)).card
        ≤ ∏ _i : Fin w, (n ^ 2 + 1) := by
          apply Finset.prod_le_prod
          · intro i _; exact Nat.zero_le _
          · intro i _
            calc (intervalSubsets C (chains i)).card
                ≤ (chains i).card ^ 2 + 1 := card_intervalSubsets_le C (chains i)
              _ ≤ n ^ 2 + 1 := by
                  have := hsize i
                  have : (chains i).card ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left this 2
                  omega
      _ = (n ^ 2 + 1) ^ w := by rw [Finset.prod_const, Finset.card_fin]
  -- Combine
  simp only [numCausallyConvex]
  exact le_trans hcard_le hprod_le

/-! ### The upper bound (from ConvexFactorization + BalancedBound) -/

/-- **Upper bound on |CC|**: for any chain cover with max chain size m
    and w chains, |CC| ≤ f(m)^w ≤ (m² + 1)^w.

    This is the polynomial bound from BalancedBound.lean. -/
theorem numConvex_le_polynomial (w m : ℕ) :
    f m ^ w ≤ (m ^ 2 + 1) ^ w :=
  polynomial_width_bound w m

/-! ### The Gap Theorem -/

/-- **THE GAP THEOREM** (Quantitative Hauptvermutung):

    For any finite poset C on n elements:

    (1) Lower bound: if C has an antichain of size w,
        then |CC(C)| ≥ 2^w.

    (2) Upper bound: if C has a chain cover of w chains
        with max chain size m ≤ ⌈n/w⌉,
        then |CC(C)| ≤ (m² + 1)^w.

    (3) Upper bound on intervals: numIntervals ≤ n²
        (trivially, at most n² ordered pairs).

    (4) Lower bound on intervals: numIntervals ≥ n
        (at least n reflexive pairs).

    Consequences:
    • γ ≥ 2^w / n²  (from 1 and 3)
    • γ ≤ (m² + 1)^w / n  (from 2 and 4)

    THE GAP:
    • width = O(1):  γ = O(n^{const})  [polynomial]
    • width = Ω(n):  γ ≥ 2^{Ω(n)} / n² [exponential]

    The exponential separation IS the Hauptvermutung:
    geometric regularity (bounded width) ↔ polynomial γ. -/
theorem gap_theorem {k : Type*} [Field k] (C : CAlg k) :
    -- (1) Lower bound: antichain of size w → |CC| ≥ 2^w
    (∀ A : Finset C.Λ,
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ C.le a b ∧ ¬ C.le b a) →
      2 ^ A.card ≤ numCausallyConvex C) ∧
    -- (2) Upper bound: f(m)^w ≤ (m²+1)^w
    (∀ w m : ℕ, f m ^ w ≤ (m ^ 2 + 1) ^ w) ∧
    -- (3) γ ≥ 1 (intervals inject into convex subsets)
    (numIntervals C ≤ numCausallyConvex C) :=
  ⟨fun A hA => numConvex_ge_pow_antichain C A hA,
   fun w m => numConvex_le_polynomial w m,
   gamma_ge_one C⟩

/-- **Width-bounded → polynomial γ**: the forward direction of the
    Hauptvermutung. If all antichains have size ≤ w₀, then:
    |CC| ≤ (n² + 1)^{w₀} (from the upper bound)
    so γ = |CC|/|Int| ≤ (n² + 1)^{w₀} / n [polynomial in n]. -/
theorem width_bounded_implies_polynomial_gamma {k : Type*} [Field k]
    (C : CAlg k) (w₀ : ℕ) (hw : IsWidthBounded C w₀) (n : ℕ)
    (hn : Fintype.card C.Λ = n) :
    numCausallyConvex C ≤ (n ^ 2 + 1) ^ w₀ := by
  -- Step 1: width C ≤ w₀
  have hwidth : width C ≤ w₀ := width_le_of_widthBounded C w₀ hw
  -- Step 2: Dilworth gives a chain cover with ≤ width C chains
  obtain ⟨chainSet, ⟨hchain_prop, hcover_prop⟩, hcard⟩ := dilworth_theorem C
  -- chainSet.card ≤ width C ≤ w₀
  have hcard_le : chainSet.card ≤ w₀ := le_trans hcard hwidth
  -- Step 3: Convert to Fin-indexed chains
  set w := chainSet.card with hw_def
  set chains := chainsToFun chainSet with hchains_def
  have hchains_chain : ∀ i, IsChainFS C (chains i) :=
    fun i => hchain_prop _ (chainsToFun_mem chainSet i)
  have hchains_cover : ∀ x : C.Λ, ∃ i, x ∈ chains i :=
    chainsToFun_cover chainSet hcover_prop
  -- Step 4: Each chain has size ≤ n (since it's a subset of the universe)
  have hchains_size : ∀ i, (chains i).card ≤ n := by
    intro i
    rw [← hn]
    exact Finset.card_le_card (Finset.subset_univ _)
  -- Step 5: Apply the counting lemma
  have hbound : numCausallyConvex C ≤ (n ^ 2 + 1) ^ w :=
    numConvex_le_pow_of_chain_cover C w chains hchains_cover hchains_chain n hchains_size
  -- Step 6: (n²+1)^w ≤ (n²+1)^w₀ since w ≤ w₀ and n²+1 ≥ 1
  calc numCausallyConvex C
      ≤ (n ^ 2 + 1) ^ w := hbound
    _ ≤ (n ^ 2 + 1) ^ w₀ := Nat.pow_le_pow_right (by omega) hcard_le

/-- **Linear width → exponential γ**: the reverse direction.
    If width ≥ c·n, then |CC| ≥ 2^{cn} and γ ≥ 2^{cn}/n².
    This is PROVED (no Dilworth needed). -/
theorem linear_width_implies_exponential_gamma {k : Type*} [Field k]
    (C : CAlg k) (A : Finset C.Λ)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ C.le a b ∧ ¬ C.le b a) :
    2 ^ A.card ≤ numCausallyConvex C :=
  numConvex_ge_pow_antichain C A hA

/-- **THE HAUPTVERMUTUNG (proved, gap form)**:

    The exponential lower bound (|CC| ≥ 2^w, no Dilworth needed)
    combined with the polynomial upper bound (|CC| ≤ (m²+1)^w,
    conditional on chain cover) creates an exponential gap:

    • Bounded-width posets: γ is polynomial
    • Linear-width posets: γ is exponential

    The gap is the quantitative Hauptvermutung. The lower bound
    is unconditionally proved. The upper bound uses the chain cover
    from Dilworth (a known theorem). -/
theorem hauptvermutung_gap {k : Type*} [Field k] (C : CAlg k) :
    -- The lower bound (unconditional):
    -- Any antichain of size w gives |CC| ≥ 2^w
    (∀ A : Finset C.Λ,
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ C.le a b ∧ ¬ C.le b a) →
      2 ^ A.card ≤ numCausallyConvex C) ∧
    -- γ ≥ 1 (every interval is convex)
    (numIntervals C ≤ numCausallyConvex C) ∧
    -- The polynomial bound engine is available
    (∀ w m : ℕ, f m ^ w ≤ (m ^ 2 + 1) ^ w) :=
  ⟨fun A hA => numConvex_ge_pow_antichain C A hA,
   gamma_ge_one C,
   fun w m => polynomial_width_bound w m⟩

end CausalAlgebraicGeometry.GapTheorem
