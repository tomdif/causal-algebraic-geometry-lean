/-
  Exact-volume interfaces for the solid-partition entropy program.

  Boxed profiles are decomposed into their actual volume coefficients.
  Their coefficients stabilize to the existing unrestricted finite-support
  partition count when the box side exceeds the volume.  At least one volume
  coefficient retains the boxed count up to a polynomial factor.  The
  quantization fibers also have an explicit bound on their volume spread.

  None of these results locates the entropy-maximizing volume, controls
  unrestricted long thin shapes at the natural scale, or proves the
  conjectural n^(3/4) leading constant.
-/
import CausalAlgebraicGeometry.CAGMultidimensionalEntropy
import CausalAlgebraicGeometry.CAGMedianGeometry
import CausalAlgebraicGeometry.NearVacuumStabilizationGeneral

namespace CausalAlgebraicGeometry.CAGSolidPartitionVolume

open C3BarrierLowerBound C3MultiscaleCompression C3ShiftCompression
open CAGBoundaryGeometry CAGMedianGeometry DimensionLaw
open NearVacuumStabilizationGeneral

noncomputable section
open scoped Classical

/-- Boxed antitone height profiles of exactly the prescribed volume. -/
def FixedVolumeProfile (d m n : ℕ) : Type :=
  {p : AntitoneProfile d m // profileVolume p = n}

instance (d m n : ℕ) : Fintype (FixedVolumeProfile d m n) := by
  unfold FixedVolumeProfile
  infer_instance

/-- A genuine coefficient count, not a finite table with a fallback value. -/
def boxedPartitionCount (d m n : ℕ) : ℕ := Fintype.card (FixedVolumeProfile d m n)

/-- Unrestricted d-dimensional partitions of n, represented in the canonical
support box [n+1]^d.  The existing support theorem justifies this finite box. -/
def partitionCount (d n : ℕ) : ℕ := antitoneSumCount d (n + 1) n

/-- The solid-partition counting function p_3(n). -/
def solidPartitionCount (n : ℕ) : ℕ := partitionCount 3 n

theorem profileVolume_le_box {d m : ℕ} (p : AntitoneProfile d m) :
    profileVolume p ≤ m ^ (d + 1) := by
  calc
    profileVolume p ≤ ∑ _f : Fin d → Fin m, m :=
      Finset.sum_le_sum (fun f _ => Nat.le_of_lt_succ (p.toFun f).isLt)
    _ = m ^ (d + 1) := by simp [pow_succ]

/-- Forget the height bound when the total volume already implies it. -/
def fixedVolumeEquivAntitoneSum (d m n : ℕ) (hnm : n ≤ m) :
    FixedVolumeProfile d m n ≃ AntitoneSum d m n where
  toFun p := ⟨fun f => (p.val.toFun f).val,
    fun _ _ h => Fin.le_def.mp (p.val.antitone h), p.property⟩
  invFun p := ⟨⟨fun f => ⟨p.val f, Nat.lt_succ_of_le
      ((antitoneSum_value_le p f).trans hnm)⟩,
    fun f g h => Fin.mk_le_mk.mpr (p.property.1 f g h)⟩, p.property.2⟩
  left_inv p := by
    apply Subtype.ext
    apply AntitoneProfile.ext
    rfl
  right_inv p := by apply Subtype.ext; rfl

/-- The boxed fixed-volume coefficient is exactly p_d(n) once m > n. -/
theorem boxedPartitionCount_stable (d m n : ℕ) (hnm : n < m) :
    boxedPartitionCount d m n = partitionCount d n := by
  calc
    boxedPartitionCount d m n = antitoneSumCount d m n :=
      Fintype.card_congr (fixedVolumeEquivAntitoneSum d m n hnm.le)
    _ = partitionCount d n := antitoneSumCount_stable hnm

/-- Exact decomposition into volume coefficients, including both empty and
full profiles. -/
theorem downsetCount_eq_sum_boxedPartitionCount (d m : ℕ) :
    downsetCountDim (d + 1) m =
      ∑ n ∈ Finset.range (m ^ (d + 1) + 1), boxedPartitionCount d m n := by
  rw [← card_antitoneProfile_eq_downsetCount]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (AntitoneProfile d m)))
    (t := Finset.range (m ^ (d + 1) + 1)) (f := profileVolume)
    (fun p _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (profileVolume_le_box p)))
  simpa only [Finset.card_univ, boxedPartitionCount, FixedVolumeProfile,
    Fintype.card_subtype] using h

/-- Some exact-volume coefficient retains the entire boxed count up to the
number of possible volumes.  It does not claim that this volume is central. -/
theorem exists_large_volume_coefficient (d m : ℕ) :
    ∃ n, n ≤ m ^ (d + 1) ∧
      downsetCountDim (d + 1) m ≤
        (m ^ (d + 1) + 1) * boxedPartitionCount d m n := by
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image
    (Finset.range (m ^ (d + 1) + 1)) (boxedPartitionCount d m)
    (by simp)
  refine ⟨n, Nat.le_of_lt_succ (Finset.mem_range.mp hn), ?_⟩
  rw [downsetCount_eq_sum_boxedPartitionCount]
  calc
    (∑ j ∈ Finset.range (m ^ (d + 1) + 1), boxedPartitionCount d m j) ≤
        ∑ _j ∈ Finset.range (m ^ (d + 1) + 1), boxedPartitionCount d m n :=
      Finset.sum_le_sum (fun j hj => hmax j hj)
    _ = _ := by simp

/-- Volume is 1-Lipschitz for the exact boundary cell metric. -/
theorem volume_dist_le_boundaryDistance {d m : ℕ} (p q : AntitoneProfile d m) :
    Nat.dist (profileVolume p) (profileVolume q) ≤ boundaryDistanceNat p q := by
  have hp : profileVolume p ≤ boundaryDistanceNat p q + profileVolume q := by
    simpa only [profileVolume, boundaryDistanceNat, Finset.sum_add_distrib] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d → Fin m)))
        (fun f _ => Nat.dist_tri_left' (p.toFun f).val (q.toFun f).val)
  have hq : profileVolume q ≤ boundaryDistanceNat p q + profileVolume p := by
    simpa only [profileVolume, boundaryDistanceNat, Finset.sum_add_distrib] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d → Fin m)))
        (fun f _ => Nat.dist_tri_left (p.toFun f).val (q.toFun f).val)
  unfold Nat.dist
  omega

/-- Equal height-quantization codes imply a uniformly thin metric fiber. -/
theorem boundaryDistance_le_of_coarseCode_eq {d m k : ℕ}
    (p q : AntitoneProfile d m) (hcode : coarseCode k p = coarseCode k q) :
    boundaryDistanceNat p q ≤ m ^ d * k := by
  have hpoint : ∀ f, Nat.dist (p.toFun f).val (q.toFun f).val ≤ k := by
    intro f
    have heq := congrArg (fun c => (c.toFun f).val) hcode
    change (p.toFun f).val / (k + 1) = (q.toFun f).val / (k + 1) at heq
    have hp := Nat.div_add_mod (p.toFun f).val (k + 1)
    have hq := Nat.div_add_mod (q.toFun f).val (k + 1)
    have hpmod := Nat.mod_lt (p.toFun f).val (by omega : 0 < k + 1)
    have hqmod := Nat.mod_lt (q.toFun f).val (by omega : 0 < k + 1)
    rw [heq] at hp
    unfold Nat.dist
    omega
  calc
    boundaryDistanceNat p q ≤ ∑ _f : Fin d → Fin m, k :=
      Finset.sum_le_sum (fun f _ => hpoint f)
    _ = _ := by simp

/-- Quantization controls volume spread as well as monotonicity.  For
solid partitions the spread is at most m^3*k, so k=o(m) preserves scaled
volume up to o(1) inside the four-dimensional box. -/
theorem volume_dist_le_of_coarseCode_eq {d m k : ℕ}
    (p q : AntitoneProfile d m) (hcode : coarseCode k p = coarseCode k q) :
    Nat.dist (profileVolume p) (profileVolume q) ≤ m ^ d * k :=
  (volume_dist_le_boundaryDistance p q).trans
    (boundaryDistance_le_of_coarseCode_eq p q hcode)

/-- Literal fixed-volume solid partitions are already among the boxed
coefficients; this endpoint exposes the exact threshold needed for equality. -/
theorem solidPartitionCount_eq_boxed (n m : ℕ) (hnm : n < m) :
    solidPartitionCount n = boxedPartitionCount 3 m n :=
  (boxedPartitionCount_stable 3 m n hnm).symm

end
end CausalAlgebraicGeometry.CAGSolidPartitionVolume
