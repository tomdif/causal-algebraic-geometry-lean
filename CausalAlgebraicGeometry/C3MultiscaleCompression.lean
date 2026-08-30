/-
  C3MultiscaleCompression.lean — Deterministic multiscale closure of the
  finite c₃ counting problem.

  The limit-shape input in C3ShiftCompression can be replaced by a purely
  combinatorial quantization.  Quantize every height in blocks of size k+1.
  The quantized profile has height at most m/(k+1), and each quantization
  fiber lies in a radius-k tube about a barrier strictly below m.  A largest
  fiber therefore contains at least the average number of profiles.

  Combining this pigeonhole step with `tube_square_le_Q_mul_thin` gives an
  exact finite inequality.  Threshold-layer encoding also gives the elementary
  thin-box bound

      #ThinProfile(2,m,k) <= C(2m,m)^k <= 4^(m*k).

  Taking k on the order of sqrt(m) makes both the coarse quantization cost and
  the two lost thin fibers subquadratic.  Thus no probabilistic limit-shape
  theorem, and no coordinate translation from lozenge heights, is needed.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.C3ShiftCompression
import CausalAlgebraicGeometry.DownsetBridge
import CausalAlgebraicGeometry.HeightBijection
import CausalAlgebraicGeometry.TightUpperBound
import Mathlib.Combinatorics.Pigeonhole

namespace CausalAlgebraicGeometry.C3MultiscaleCompression

open CausalAlgebraicGeometry.C3BarrierLowerBound
open CausalAlgebraicGeometry.C3Conjecture
open CausalAlgebraicGeometry.C3ShiftCompression
open CausalAlgebraicGeometry.DimensionLaw
open CausalAlgebraicGeometry.DownsetBridge
open CausalAlgebraicGeometry.HeightBijection
open CausalAlgebraicGeometry.TightUpperBound

noncomputable section
open scoped Classical

/-! ## Thin profiles are chains of ordinary downsets -/

/-- The finite type of downsets in `[m]^d`.  It is packaged as the coercion of
the same filtered powerset whose cardinality defines `downsetCountDim`. -/
def DownsetProfile (d m : ℕ) : Type :=
  ↑((Finset.univ : Finset (Fin d → Fin m)).powerset.filter (IsDownsetDim d m))

instance (d m : ℕ) : Fintype (DownsetProfile d m) := by
  unfold DownsetProfile
  infer_instance

theorem card_downsetProfile (d m : ℕ) :
    Fintype.card (DownsetProfile d m) = downsetCountDim d m := by
  unfold DownsetProfile downsetCountDim
  exact Fintype.card_coe _

/-- The `ell`-th threshold layer `{x | ell < p(x)}` of an antitone profile is
a downset. -/
def thresholdLayer {d m k : ℕ} (p : ThinProfile d m k) (ell : Fin k) :
    DownsetProfile d m := by
  let D : Finset (Fin d → Fin m) :=
    Finset.univ.filter fun f => ell.val < (p.toFun f).val
  refine ⟨D, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
  intro f hf g hgf
  simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
  exact lt_of_lt_of_le hf (Fin.le_def.mp (p.antitone hgf))

/-- All threshold layers determine the original integer height profile. -/
theorem thresholdLayers_injective {d m k : ℕ} :
    Function.Injective
      (fun p : ThinProfile d m k => fun ell : Fin k => thresholdLayer p ell) := by
  intro p q hpq
  apply ThinProfile.ext
  funext f
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hp_lt | hq_lt
  · have hp_k : (p.toFun f).val < k := by
      have hq_le : (q.toFun f).val ≤ k := Nat.le_of_lt_succ (q.toFun f).isLt
      omega
    let ell : Fin k := ⟨(p.toFun f).val, hp_k⟩
    have hmem_q : f ∈ (thresholdLayer q ell).val := by
      simpa [thresholdLayer, ell] using
        (show p.toFun f < q.toFun f from Fin.mk_lt_mk.mpr hp_lt)
    have hnot_p : f ∉ (thresholdLayer p ell).val := by
      simp [thresholdLayer, ell]
    have heq : (thresholdLayer p ell).val = (thresholdLayer q ell).val :=
      congrArg Subtype.val (congrFun hpq ell)
    apply hnot_p
    rw [heq]
    exact hmem_q
  · have hq_k : (q.toFun f).val < k := by
      have hp_le : (p.toFun f).val ≤ k := Nat.le_of_lt_succ (p.toFun f).isLt
      omega
    let ell : Fin k := ⟨(q.toFun f).val, hq_k⟩
    have hmem_p : f ∈ (thresholdLayer p ell).val := by
      simpa [thresholdLayer, ell] using
        (show q.toFun f < p.toFun f from Fin.mk_lt_mk.mpr hq_lt)
    have hnot_q : f ∉ (thresholdLayer q ell).val := by
      simp [thresholdLayer, ell]
    have heq : (thresholdLayer p ell).val = (thresholdLayer q ell).val :=
      congrArg Subtype.val (congrFun hpq ell)
    apply hnot_q
    rw [← heq]
    exact hmem_p

/-- A thin `d`-dimensional height profile is bounded by a `k`-tuple of
downsets of its base. -/
theorem thinProfile_card_le_downset_pow (d m k : ℕ) :
    Fintype.card (ThinProfile d m k) ≤ downsetCountDim d m ^ k := by
  calc
    Fintype.card (ThinProfile d m k)
        ≤ Fintype.card (Fin k → DownsetProfile d m) :=
      Fintype.card_le_of_injective _ thresholdLayers_injective
    _ = Fintype.card (DownsetProfile d m) ^ k := by
      simp
    _ = downsetCountDim d m ^ k := by rw [card_downsetProfile]

/-- In base dimension two, every thin profile costs at most `4^(m*k)`.
This replaces the rectangular MacMahon estimate by an elementary layer
encoding and the central-binomial bound. -/
theorem thinProfile_card_le_four_pow (m k : ℕ) :
    Fintype.card (ThinProfile 2 m k) ≤ 4 ^ (m * k) := by
  calc
    Fintype.card (ThinProfile 2 m k)
        ≤ downsetCountDim 2 m ^ k := thinProfile_card_le_downset_pow 2 m k
    _ = Nat.choose (2 * m) m ^ k := by rw [downsetCountDim_two_eq_choose]
    _ ≤ (4 ^ m) ^ k := Nat.pow_le_pow_left (choose_central_le_four_pow m) k
    _ = 4 ^ (m * k) := by rw [pow_mul]

/-- Regard a thin profile as a full-height profile when its height bound fits
inside the ambient box. -/
def thinToAntitoneProfile {d m k : ℕ} (hkm : k ≤ m) (p : ThinProfile d m k) :
    AntitoneProfile d m where
  toFun f := ⟨(p.toFun f).val, by
    have := (p.toFun f).isLt
    omega⟩
  antitone := by
    intro f g hfg
    exact Fin.mk_le_mk.mpr (Fin.le_def.mp (p.antitone hfg))

theorem thinToAntitoneProfile_injective {d m k : ℕ} (hkm : k ≤ m) :
    Function.Injective (thinToAntitoneProfile (d := d) (m := m) hkm) := by
  intro p q hpq
  apply ThinProfile.ext
  funext f
  apply Fin.ext
  exact congrArg (fun r => (r.toFun f).val) hpq

theorem thinProfile_card_le_antitoneProfile (d m k : ℕ) (hkm : k ≤ m) :
    Fintype.card (ThinProfile d m k) ≤ Fintype.card (AntitoneProfile d m) :=
  Fintype.card_le_of_injective (thinToAntitoneProfile hkm)
    (thinToAntitoneProfile_injective hkm)

/-! ## Cubic plane partitions are exactly full-height profiles -/

/-- The filtered finite type of all antitone height functions. -/
def AntitoneFamily (d m : ℕ) : Type :=
  ↑((Finset.univ : Finset ((Fin d → Fin m) → Fin (m + 1))).filter Antitone)

instance (d m : ℕ) : Fintype (AntitoneFamily d m) := by
  unfold AntitoneFamily
  infer_instance

/-- `AntitoneProfile` is only a structure wrapper around `AntitoneFamily`. -/
def profileEquivFamily (d m : ℕ) : AntitoneProfile d m ≃ AntitoneFamily d m where
  toFun p := ⟨p.toFun, by simp [p.antitone]⟩
  invFun p := ⟨p.val, (Finset.mem_filter.mp p.property).2⟩
  left_inv p := by cases p; rfl
  right_inv p := by apply Subtype.ext; rfl

/-- The number of full-height profiles is the cubic plane-partition/downset
count, with no coordinate convention left implicit. -/
theorem card_antitoneProfile_eq_downsetCount (d m : ℕ) :
    Fintype.card (AntitoneProfile d m) = downsetCountDim (d + 1) m := by
  calc
    Fintype.card (AntitoneProfile d m) = Fintype.card (AntitoneFamily d m) :=
      Fintype.card_congr (profileEquivFamily d m)
    _ = ((Finset.univ : Finset ((Fin d → Fin m) → Fin (m + 1))).filter Antitone).card :=
      Fintype.card_coe _
    _ = downsetCountDim (d + 1) m :=
      (downsetCountDim_eq_antitone_count d m).symm

/-! ## Deterministic height quantization -/

/-- Quantize heights into blocks of size `k+1`. -/
def coarseCode {d m : ℕ} (k : ℕ) (p : AntitoneProfile d m) :
    ThinProfile d m (m / (k + 1)) where
  toFun f := ⟨(p.toFun f).val / (k + 1), by
    apply Nat.lt_succ_of_le
    exact Nat.div_le_div_right (Nat.le_of_lt_succ (p.toFun f).isLt)⟩
  antitone := by
    intro f g hfg
    apply Fin.mk_le_mk.mpr
    exact Nat.div_le_div_right (Fin.le_def.mp (p.antitone hfg))

instance (d m k : ℕ) : Nonempty (ThinProfile d m k) :=
  ⟨⟨fun _ => 0, fun _ _ _ => le_rfl⟩⟩

/-- Turn a coarse code into a barrier.  Clipping at `m-1` ensures the strict
upper shift is available even when the top quantization block meets height
`m`. -/
def coarseBarrier {d m : ℕ} (k : ℕ)
    (q : ThinProfile d m (m / (k + 1))) : (Fin d → Fin m) → ℕ :=
  fun f => min ((k + 1) * (q.toFun f).val) (m - 1)

theorem coarseBarrier_lt {d m k : ℕ} (hm : 0 < m)
    (q : ThinProfile d m (m / (k + 1))) (f : Fin d → Fin m) :
    coarseBarrier k q f < m := by
  unfold coarseBarrier
  omega

/-- A profile lies in the radius-`k` tube selected by its own coarse code. -/
theorem mem_tube_coarseCode {d m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (p : AntitoneProfile d m) :
    ∀ f,
      (p.toFun f).val ≤ coarseBarrier k (coarseCode k p) f + k ∧
      coarseBarrier k (coarseCode k p) f ≤ (p.toFun f).val + k := by
  intro f
  let h := (p.toFun f).val
  have hh_le : h ≤ m := Nat.le_of_lt_succ (p.toFun f).isLt
  have hs_pos : 0 < k + 1 := by omega
  have hdecomp : (k + 1) * (h / (k + 1)) + h % (k + 1) = h := by
    simpa [Nat.mul_comm] using Nat.div_add_mod h (k + 1)
  have hrem : h % (k + 1) < k + 1 := Nat.mod_lt _ hs_pos
  have hbase_le : (k + 1) * (h / (k + 1)) ≤ h := by omega
  have hdist : h ≤ (k + 1) * (h / (k + 1)) + k := by omega
  change h ≤ min ((k + 1) * (h / (k + 1))) (m - 1) + k ∧
    min ((k + 1) * (h / (k + 1))) (m - 1) ≤ h + k
  constructor
  · by_cases htop : (k + 1) * (h / (k + 1)) ≤ m - 1
    · rw [min_eq_left htop]
      exact hdist
    · rw [min_eq_right (Nat.le_of_not_ge htop)]
      omega
  · exact le_trans (min_le_left _ _) (le_trans hbase_le (Nat.le_add_right _ _))

/-- The fiber of the coarse-code map over `q`. -/
def CoarseFiber {d m : ℕ} (k : ℕ) (q : ThinProfile d m (m / (k + 1))) : Type :=
  {p : AntitoneProfile d m // coarseCode k p = q}

instance {d m : ℕ} (k : ℕ) (q : ThinProfile d m (m / (k + 1))) :
    Fintype (CoarseFiber k q) := by
  unfold CoarseFiber
  infer_instance

/-- A coarse-code fiber injects into the corresponding geometric tube. -/
def coarseFiberToTube {d m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (q : ThinProfile d m (m / (k + 1))) :
    CoarseFiber k q → LimitTube d m (coarseBarrier k q) k :=
  fun p => ⟨p.val, by
    intro f
    have h := mem_tube_coarseCode hm hk p.val f
    simpa only [p.property] using h⟩

theorem coarseFiberToTube_injective {d m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (q : ThinProfile d m (m / (k + 1))) :
    Function.Injective (coarseFiberToTube hm hk q) := by
  intro p r h
  apply Subtype.ext
  exact congrArg (fun z : LimitTube d m (coarseBarrier k q) k => z.val) h

/-! ## The finite multiscale inequality -/

/-- Some quantization fiber has at least the floor of the average size. -/
theorem exists_large_coarseFiber (d m k : ℕ) :
    ∃ q : ThinProfile d m (m / (k + 1)),
      Fintype.card (AntitoneProfile d m) /
          Fintype.card (ThinProfile d m (m / (k + 1))) ≤
        Fintype.card (CoarseFiber k q) := by
  let C := Fintype.card (ThinProfile d m (m / (k + 1)))
  let N := Fintype.card (AntitoneProfile d m)
  have hmul : C * (N / C) ≤ N := Nat.mul_div_le _ _
  have hcards :
      Fintype.card (ThinProfile d m (m / (k + 1))) *
          (Fintype.card (AntitoneProfile d m) /
            Fintype.card (ThinProfile d m (m / (k + 1)))) ≤
        Fintype.card (AntitoneProfile d m) := by
    simpa [C, N] using hmul
  obtain ⟨q, hq⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (f := coarseCode k) hcards
  refine ⟨q, ?_⟩
  unfold CoarseFiber
  rw [Fintype.card_subtype]
  exact hq

/-- Elementary floor control: if `0 < C ≤ N`, twice the floored average
still covers `N`. -/
theorem le_two_mul_floor_average (N C : ℕ) (hC : 0 < C) (hCN : C ≤ N) :
    N ≤ 2 * C * (N / C) := by
  have hdiv : C * (N / C) + N % C = N := by
    simpa [Nat.mul_comm] using Nat.div_add_mod N C
  have hmod : N % C < C := Nat.mod_lt _ hC
  have hq : 1 ≤ N / C := (Nat.one_le_div_iff hC).mpr hCN
  have hCq : C ≤ C * (N / C) := by
    simpa using Nat.mul_le_mul_left C hq
  calc
    N = C * (N / C) + N % C := hdiv.symm
    _ ≤ C * (N / C) + C := Nat.add_le_add_left (Nat.le_of_lt hmod) _
    _ ≤ C * (N / C) + C * (N / C) := Nat.add_le_add_left hCq _
    _ = 2 * C * (N / C) := by ring

/-- **MULTISCALE COMPRESSION, FINITE FORM.**  The square of the average
coarse fiber is bounded by `Q(m)` times two thin-profile losses. -/
theorem average_coarseFiber_square_le (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (Fintype.card (AntitoneProfile 2 m) /
        Fintype.card (ThinProfile 2 m (m / (k + 1)))) ^ 2 ≤
      Q m * (Fintype.card (ThinProfile 2 m k) *
        Fintype.card (ThinProfile 2 m (k + 1))) := by
  obtain ⟨q, hq⟩ := exists_large_coarseFiber 2 m k
  have hfiber_tube : Fintype.card (CoarseFiber k q) ≤
      Fintype.card (LimitTube 2 m (coarseBarrier k q) k) :=
    Fintype.card_le_of_injective (coarseFiberToTube hm hk q)
      (coarseFiberToTube_injective hm hk q)
  have htube := tube_square_le_Q_mul_thin m k (coarseBarrier k q)
    (coarseBarrier_lt hm q)
  exact le_trans (Nat.pow_le_pow_left (le_trans hq hfiber_tube) 2) htube

/-- The same theorem with the cubic downset count exposed explicitly. -/
theorem downset_average_square_le (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (downsetCountDim 3 m /
        Fintype.card (ThinProfile 2 m (m / (k + 1)))) ^ 2 ≤
      Q m * (Fintype.card (ThinProfile 2 m k) *
        Fintype.card (ThinProfile 2 m (k + 1))) := by
  simpa [card_antitoneProfile_eq_downsetCount] using
    average_coarseFiber_square_le m k hm hk

/-- Remove the floor-average denominator at the cost of a harmless factor
four.  This is the most convenient exact inequality for taking logarithms. -/
theorem profile_square_le_multiscale_correction (m k : ℕ)
    (hm : 0 < m) (hk : 0 < k) :
    Fintype.card (AntitoneProfile 2 m) ^ 2 ≤
      4 * Fintype.card (ThinProfile 2 m (m / (k + 1))) ^ 2 *
        (Q m * (Fintype.card (ThinProfile 2 m k) *
          Fintype.card (ThinProfile 2 m (k + 1)))) := by
  let N := Fintype.card (AntitoneProfile 2 m)
  let C := Fintype.card (ThinProfile 2 m (m / (k + 1)))
  let A := N / C
  have hC : 0 < C := by
    exact Fintype.card_pos_iff.mpr inferInstance
  have hr_le : m / (k + 1) ≤ m := Nat.div_le_self _ _
  have hCN : C ≤ N := by
    exact thinProfile_card_le_antitoneProfile 2 m (m / (k + 1)) hr_le
  have hN : N ≤ 2 * C * A := le_two_mul_floor_average N C hC hCN
  have hA : A ^ 2 ≤
      Q m * (Fintype.card (ThinProfile 2 m k) *
        Fintype.card (ThinProfile 2 m (k + 1))) := by
    simpa [N, C, A] using average_coarseFiber_square_le m k hm hk
  calc
    N ^ 2 ≤ (2 * C * A) ^ 2 := Nat.pow_le_pow_left hN 2
    _ = 4 * C ^ 2 * A ^ 2 := by ring
    _ ≤ 4 * C ^ 2 *
        (Q m * (Fintype.card (ThinProfile 2 m k) *
          Fintype.card (ThinProfile 2 m (k + 1)))) :=
      Nat.mul_le_mul_left _ hA

/-- Fully elementary correction bound.  With `k ≍ sqrt(m)`, every exponent
on the right is `O(m^(3/2))`, hence negligible relative to `m²`. -/
theorem downset_square_le_explicit_correction (m k : ℕ)
    (hm : 0 < m) (hk : 0 < k) :
    downsetCountDim 3 m ^ 2 ≤
      4 * (4 ^ (m * (m / (k + 1)))) ^ 2 *
        (Q m * (4 ^ (m * k) * 4 ^ (m * (k + 1)))) := by
  have hmain := profile_square_le_multiscale_correction m k hm hk
  have hcoarse := thinProfile_card_le_four_pow m (m / (k + 1))
  have hkthin := thinProfile_card_le_four_pow m k
  have hksucc := thinProfile_card_le_four_pow m (k + 1)
  have hleft :
      4 * Fintype.card (ThinProfile 2 m (m / (k + 1))) ^ 2 ≤
        4 * (4 ^ (m * (m / (k + 1)))) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcoarse 2)
  have hright :
      Q m * (Fintype.card (ThinProfile 2 m k) *
        Fintype.card (ThinProfile 2 m (k + 1))) ≤
      Q m * (4 ^ (m * k) * 4 ^ (m * (k + 1))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hkthin hksucc)
  rw [card_antitoneProfile_eq_downsetCount] at hmain
  exact le_trans hmain (Nat.mul_le_mul hleft hright)

/-- Compact power-of-four form of the explicit correction. -/
theorem downset_square_le_power_correction (m k : ℕ)
    (hm : 0 < m) (hk : 0 < k) :
    downsetCountDim 3 m ^ 2 ≤
      Q m * 4 ^ (1 + 2 * (m * (m / (k + 1))) + m * k + m * (k + 1)) := by
  have h := downset_square_le_explicit_correction m k hm hk
  calc
    downsetCountDim 3 m ^ 2
        ≤ 4 * (4 ^ (m * (m / (k + 1)))) ^ 2 *
          (Q m * (4 ^ (m * k) * 4 ^ (m * (k + 1)))) := h
    _ = Q m * 4 ^
        (1 + 2 * (m * (m / (k + 1))) + m * k + m * (k + 1)) := by
      have hexp :
          1 + 2 * (m * (m / (k + 1))) + m * k + m * (k + 1) =
            1 + (m * (m / (k + 1))) + (m * (m / (k + 1))) +
              m * k + m * (k + 1) := by omega
      rw [hexp]
      simp only [pow_two, pow_add, pow_one]
      ring

/-! The exact theorem above is the new combinatorial core.  Its elementary
power bounds imply an `exp(O(m²/k + mk))` total correction.  The real-log
limit packaging is kept separate so that it can be audited independently of
the finite injection argument. -/

end
end CausalAlgebraicGeometry.C3MultiscaleCompression
