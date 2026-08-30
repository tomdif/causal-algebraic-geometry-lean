/-
  CAGMedianGeometry.lean — Distributive-lattice and median geometry of CAG
  boundary profiles.

  Antitone height profiles are not merely points carrying an L¹ distance.
  Pointwise minimum and maximum remain antitone, so the state space is a
  finite bounded distributive lattice.  Its cell volume is a valuation, and
  the boundary distance is exactly the corresponding valuation metric.

  The majority term

      med(p,q,r) = (p ⊓ q) ⊔ (q ⊓ r) ⊔ (r ⊓ p)

  is therefore intrinsic to the causal order.  We prove that it lies on a
  shortest metric interval between each pair.  This supplies a canonical
  nonlinear interpolation of three causal boundary states without choosing
  coordinates in an ambient continuum.

  Zero sorry.  No custom axioms.
-/
import CausalAlgebraicGeometry.CAGBoundaryGeometry
import Mathlib.Order.Lattice

namespace CausalAlgebraicGeometry.CAGMedianGeometry

open CausalAlgebraicGeometry.C3BarrierLowerBound
open CausalAlgebraicGeometry.CAGBoundaryGeometry

noncomputable section
open scoped Classical

/-! ## The finite bounded distributive lattice of profiles -/

/-- The intrinsic order on boundary states is pointwise inclusion of their
subgraphs. -/
instance {d m : ℕ} : LE (AntitoneProfile d m) where
  le p q := ∀ f, p.toFun f ≤ q.toFun f

@[simp]
theorem profile_le_iff {d m : ℕ} (p q : AntitoneProfile d m) :
    p ≤ q ↔ ∀ f, p.toFun f ≤ q.toFun f := Iff.rfl

instance {d m : ℕ} : PartialOrder (AntitoneProfile d m) where
  le_refl p f := le_rfl
  le_trans p q r hpq hqr f := le_trans (hpq f) (hqr f)
  le_antisymm p q hpq hqp := by
    apply AntitoneProfile.ext
    funext f
    exact le_antisymm (hpq f) (hqp f)

/-- Pointwise intersection of the subgraphs of two profiles. -/
def profileMeet {d m : ℕ} (p q : AntitoneProfile d m) :
    AntitoneProfile d m where
  toFun f := ⟨min (p.toFun f).val (q.toFun f).val,
    lt_of_le_of_lt (min_le_left _ _) (p.toFun f).isLt⟩
  antitone := by
    intro f g hfg
    apply Fin.mk_le_mk.mpr
    have hp := Fin.le_def.mp (p.antitone hfg)
    have hq := Fin.le_def.mp (q.antitone hfg)
    omega

/-- Pointwise union of the subgraphs of two profiles. -/
def profileJoin {d m : ℕ} (p q : AntitoneProfile d m) :
    AntitoneProfile d m where
  toFun f := ⟨max (p.toFun f).val (q.toFun f).val,
    max_lt (p.toFun f).isLt (q.toFun f).isLt⟩
  antitone := by
    intro f g hfg
    apply Fin.mk_le_mk.mpr
    have hp := Fin.le_def.mp (p.antitone hfg)
    have hq := Fin.le_def.mp (q.antitone hfg)
    omega

@[simp]
theorem profileMeet_val {d m : ℕ} (p q : AntitoneProfile d m)
    (f : Fin d → Fin m) :
    ((profileMeet p q).toFun f).val =
      min (p.toFun f).val (q.toFun f).val := rfl

@[simp]
theorem profileJoin_val {d m : ℕ} (p q : AntitoneProfile d m)
    (f : Fin d → Fin m) :
    ((profileJoin p q).toFun f).val =
      max (p.toFun f).val (q.toFun f).val := rfl

instance {d m : ℕ} : Lattice (AntitoneProfile d m) where
  sup := profileJoin
  le_sup_left p q f := by
    apply Fin.mk_le_mk.mpr
    exact le_max_left _ _
  le_sup_right p q f := by
    apply Fin.mk_le_mk.mpr
    exact le_max_right _ _
  sup_le p q r hpr hqr f := by
    apply Fin.mk_le_mk.mpr
    exact max_le (Fin.le_def.mp (hpr f)) (Fin.le_def.mp (hqr f))
  inf := profileMeet
  inf_le_left p q f := by
    apply Fin.mk_le_mk.mpr
    exact min_le_left _ _
  inf_le_right p q f := by
    apply Fin.mk_le_mk.mpr
    exact min_le_right _ _
  le_inf p q r hpq hpr f := by
    apply Fin.mk_le_mk.mpr
    exact le_min (Fin.le_def.mp (hpq f)) (Fin.le_def.mp (hpr f))

instance {d m : ℕ} : DistribLattice (AntitoneProfile d m) where
  le_sup_inf p q r f := by
    apply Fin.mk_le_mk.mpr
    change min (max (p.toFun f).val (q.toFun f).val)
      (max (p.toFun f).val (r.toFun f).val) ≤
      max (p.toFun f).val (min (q.toFun f).val (r.toFun f).val)
    omega

@[simp]
theorem profile_inf_val {d m : ℕ} (p q : AntitoneProfile d m)
    (f : Fin d → Fin m) :
    (((p ⊓ q).toFun f).val) =
      min (p.toFun f).val (q.toFun f).val := rfl

@[simp]
theorem profile_sup_val {d m : ℕ} (p q : AntitoneProfile d m)
    (f : Fin d → Fin m) :
    (((p ⊔ q).toFun f).val) =
      max (p.toFun f).val (q.toFun f).val := rfl

/-- Empty boundary subgraph. -/
def emptyProfile (d m : ℕ) : AntitoneProfile d m where
  toFun _ := ⟨0, Nat.zero_lt_succ m⟩
  antitone := fun _ _ _ => le_rfl

/-- Full boundary subgraph. -/
def fullProfile (d m : ℕ) : AntitoneProfile d m where
  toFun _ := ⟨m, Nat.lt_succ_self m⟩
  antitone := fun _ _ _ => le_rfl

instance {d m : ℕ} : OrderBot (AntitoneProfile d m) where
  bot := emptyProfile d m
  bot_le p f := by
    apply Fin.mk_le_mk.mpr
    exact Nat.zero_le _

instance {d m : ℕ} : OrderTop (AntitoneProfile d m) where
  top := fullProfile d m
  le_top p f := by
    apply Fin.mk_le_mk.mpr
    exact Nat.le_of_lt_succ (p.toFun f).isLt

/-! ## The L¹ metric is the lattice valuation metric -/

/-- Number of unit cells below a boundary profile. -/
def profileVolume {d m : ℕ} (p : AntitoneProfile d m) : ℕ :=
  ∑ f : Fin d → Fin m, (p.toFun f).val

/-- Cell volume is a lattice valuation. -/
theorem profileVolume_inf_add_sup {d m : ℕ} (p q : AntitoneProfile d m) :
    profileVolume (p ⊓ q) + profileVolume (p ⊔ q) =
      profileVolume p + profileVolume q := by
  unfold profileVolume
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  exact min_add_max (p.toFun f).val (q.toFun f).val

/-- Exact rank formula: distance is the volume gained between meet and join. -/
theorem boundaryDistanceNat_eq_sup_volume_sub_inf {d m : ℕ}
    (p q : AntitoneProfile d m) :
    boundaryDistanceNat p q = profileVolume (p ⊔ q) - profileVolume (p ⊓ q) := by
  unfold boundaryDistanceNat profileVolume
  simp_rw [Nat.dist_eq_max_sub_min]
  rw [Finset.sum_tsub_distrib]
  · simp only [profile_sup_val, profile_inf_val]
  · intro f _
    exact min_le_max

/-- Comparable profiles have distance equal to their rank difference. -/
theorem boundaryDistanceNat_of_le {d m : ℕ} {p q : AntitoneProfile d m}
    (hpq : p ≤ q) :
    boundaryDistanceNat p q = profileVolume q - profileVolume p := by
  rw [boundaryDistanceNat_eq_sup_volume_sub_inf, sup_eq_right.mpr hpq,
    inf_eq_left.mpr hpq]

/-- The meet is on a metric geodesic from `p` to `q`. -/
theorem boundaryDistanceNat_split_inf {d m : ℕ}
    (p q : AntitoneProfile d m) :
    boundaryDistanceNat p q =
      boundaryDistanceNat p (p ⊓ q) + boundaryDistanceNat (p ⊓ q) q := by
  unfold boundaryDistanceNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  simp only [profile_inf_val, Nat.dist]
  omega

/-- The join gives a second canonical metric geodesic from `p` to `q`. -/
theorem boundaryDistanceNat_split_sup {d m : ℕ}
    (p q : AntitoneProfile d m) :
    boundaryDistanceNat p q =
      boundaryDistanceNat p (p ⊔ q) + boundaryDistanceNat (p ⊔ q) q := by
  unfold boundaryDistanceNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  simp only [profile_sup_val, Nat.dist]
  omega

/-! ## Canonical median interpolation -/

/-- Majority/median of three causal boundary states. -/
def profileMedian {d m : ℕ} (p q r : AntitoneProfile d m) :
    AntitoneProfile d m :=
  (p ⊓ q) ⊔ ((q ⊓ r) ⊔ (r ⊓ p))

@[simp]
theorem profileMedian_val {d m : ℕ} (p q r : AntitoneProfile d m)
    (f : Fin d → Fin m) :
    ((profileMedian p q r).toFun f).val =
      max (min (p.toFun f).val (q.toFun f).val)
        (max (min (q.toFun f).val (r.toFun f).val)
          (min (r.toFun f).val (p.toFun f).val)) := rfl

private theorem nat_dist_split_of_between {a b x : ℕ}
    (hlo : min a b ≤ x) (hhi : x ≤ max a b) :
    Nat.dist a b = Nat.dist a x + Nat.dist x b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab] at hlo
    rw [max_eq_right hab] at hhi
    rw [Nat.dist_eq_sub_of_le hab, Nat.dist_eq_sub_of_le hlo,
      Nat.dist_eq_sub_of_le hhi]
    omega
  · rw [min_eq_right hba] at hlo
    rw [max_eq_left hba] at hhi
    rw [Nat.dist_eq_sub_of_le_right hhi,
      Nat.dist_eq_sub_of_le_right hlo, Nat.dist_eq_sub_of_le_right hba]
    omega

private theorem nat_dist_median_split (a b c : ℕ) :
    let μ := max (min a b) (max (min b c) (min c a))
    Nat.dist a b = Nat.dist a μ + Nat.dist μ b := by
  dsimp
  apply nat_dist_split_of_between
  · exact le_max_left _ _
  · apply max_le
    · exact min_le_max
    · apply max_le
      · exact (min_le_left b c).trans (le_max_right a b)
      · exact (min_le_right c a).trans (le_max_left a b)

/-- The CAG median lies on a shortest metric interval from `p` to `q`. -/
theorem profileMedian_on_geodesic_pq {d m : ℕ}
    (p q r : AntitoneProfile d m) :
    boundaryDistanceNat p q =
      boundaryDistanceNat p (profileMedian p q r) +
        boundaryDistanceNat (profileMedian p q r) q := by
  unfold boundaryDistanceNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  exact nat_dist_median_split _ _ _

/-- The same median lies on a shortest interval from `q` to `r`. -/
theorem profileMedian_on_geodesic_qr {d m : ℕ}
    (p q r : AntitoneProfile d m) :
    boundaryDistanceNat q r =
      boundaryDistanceNat q (profileMedian p q r) +
        boundaryDistanceNat (profileMedian p q r) r := by
  unfold boundaryDistanceNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  simpa only [profileMedian_val, max_comm, max_left_comm, max_assoc] using
    nat_dist_median_split (q.toFun f).val (r.toFun f).val (p.toFun f).val

/-- The same median lies on a shortest interval from `r` to `p`. -/
theorem profileMedian_on_geodesic_rp {d m : ℕ}
    (p q r : AntitoneProfile d m) :
    boundaryDistanceNat r p =
      boundaryDistanceNat r (profileMedian p q r) +
        boundaryDistanceNat (profileMedian p q r) p := by
  unfold boundaryDistanceNat
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  simpa only [profileMedian_val, max_comm, max_left_comm, max_assoc] using
    nat_dist_median_split (r.toFun f).val (p.toFun f).val (q.toFun f).val

/-- Package of the three simultaneous geodesic identities.  This is the
median-geometry theorem used by downstream CAG constructions. -/
theorem profileMedian_three_geodesics {d m : ℕ}
    (p q r : AntitoneProfile d m) :
    (boundaryDistanceNat p q =
      boundaryDistanceNat p (profileMedian p q r) +
        boundaryDistanceNat (profileMedian p q r) q) ∧
    (boundaryDistanceNat q r =
      boundaryDistanceNat q (profileMedian p q r) +
        boundaryDistanceNat (profileMedian p q r) r) ∧
    (boundaryDistanceNat r p =
      boundaryDistanceNat r (profileMedian p q r) +
        boundaryDistanceNat (profileMedian p q r) p) :=
  ⟨profileMedian_on_geodesic_pq p q r,
    profileMedian_on_geodesic_qr p q r,
    profileMedian_on_geodesic_rp p q r⟩

/-! ## Uniqueness of the metric median -/

/-- A boundary state lies on the metric interval between two others when the
triangle inequality is saturated through that state. -/
def OnBoundaryInterval {d m : ℕ} (p x q : AntitoneProfile d m) : Prop :=
  boundaryDistanceNat p q = boundaryDistanceNat p x + boundaryDistanceNat x q

/-- Saturation of the global L¹ triangle inequality forces saturation in
every individual height coordinate. -/
theorem onBoundaryInterval_pointwise {d m : ℕ}
    {p x q : AntitoneProfile d m} (h : OnBoundaryInterval p x q)
    (f : Fin d → Fin m) :
    Nat.dist (p.toFun f).val (q.toFun f).val =
      Nat.dist (p.toFun f).val (x.toFun f).val +
        Nat.dist (x.toFun f).val (q.toFun f).val := by
  have hsum :
      (∑ i : Fin d → Fin m,
        (Nat.dist (p.toFun i).val (x.toFun i).val +
          Nat.dist (x.toFun i).val (q.toFun i).val -
          Nat.dist (p.toFun i).val (q.toFun i).val)) = 0 := by
    rw [Finset.sum_tsub_distrib]
    · rw [Finset.sum_add_distrib]
      unfold OnBoundaryInterval boundaryDistanceNat at h
      rw [← h]
      exact Nat.sub_self _
    · intro i _
      exact Nat.dist.triangle_inequality _ _ _
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (s := (Finset.univ : Finset (Fin d → Fin m)))
    (f := fun i =>
      Nat.dist (p.toFun i).val (x.toFun i).val +
        Nat.dist (x.toFun i).val (q.toFun i).val -
        Nat.dist (p.toFun i).val (q.toFun i).val)
    (fun _ _ => Nat.zero_le _)).mp hsum
  have hreverse :
      Nat.dist (p.toFun f).val (x.toFun f).val +
          Nat.dist (x.toFun f).val (q.toFun f).val ≤
        Nat.dist (p.toFun f).val (q.toFun f).val :=
    Nat.sub_eq_zero_iff_le.mp (hall f (Finset.mem_univ f))
  exact le_antisymm (Nat.dist.triangle_inequality _ _ _) hreverse

private theorem nat_between_of_dist_split {a b x : ℕ}
    (h : Nat.dist a b = Nat.dist a x + Nat.dist x b) :
    min a b ≤ x ∧ x ≤ max a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    simp only [Nat.dist] at h
    omega
  · rw [min_eq_right hba, max_eq_left hba]
    simp only [Nat.dist] at h
    omega

private theorem nat_eq_median_of_three_splits {a b c x : ℕ}
    (hab : Nat.dist a b = Nat.dist a x + Nat.dist x b)
    (hbc : Nat.dist b c = Nat.dist b x + Nat.dist x c)
    (hca : Nat.dist c a = Nat.dist c x + Nat.dist x a) :
    x = max (min a b) (max (min b c) (min c a)) := by
  have hab' := nat_between_of_dist_split hab
  have hbc' := nat_between_of_dist_split hbc
  have hca' := nat_between_of_dist_split hca
  apply le_antisymm
  · have hx : x ≤
        min (max a b) (min (max b c) (max c a)) :=
      le_min hab'.2 (le_min hbc'.2 hca'.2)
    have hmajority :
        min (max a b) (min (max b c) (max c a)) =
          max (min a b) (max (min b c) (min c a)) := by
      omega
    rwa [hmajority] at hx
  · exact max_le hab'.1 (max_le hbc'.1 hca'.1)

/-- The three-profile majority is the unique common point of the three metric
intervals.  Thus the CAG boundary state space is a genuine finite median
metric geometry, not only a metric lattice with a chosen ternary operation. -/
theorem profileMedian_unique {d m : ℕ}
    (p q r x : AntitoneProfile d m)
    (hpq : OnBoundaryInterval p x q)
    (hqr : OnBoundaryInterval q x r)
    (hrp : OnBoundaryInterval r x p) :
    x = profileMedian p q r := by
  apply AntitoneProfile.ext
  funext f
  apply Fin.ext
  exact nat_eq_median_of_three_splits
    (onBoundaryInterval_pointwise hpq f)
    (onBoundaryInterval_pointwise hqr f)
    (onBoundaryInterval_pointwise hrp f)

/-- Existence-and-uniqueness package for the intrinsic median of every triple
of CAG boundary states. -/
theorem existsUnique_profileMedian {d m : ℕ}
    (p q r : AntitoneProfile d m) :
    ∃! x : AntitoneProfile d m,
      OnBoundaryInterval p x q ∧
      OnBoundaryInterval q x r ∧
      OnBoundaryInterval r x p := by
  refine ⟨profileMedian p q r, ?_, ?_⟩
  · exact profileMedian_three_geodesics p q r
  · intro x hx
    exact profileMedian_unique p q r x hx.1 hx.2.1 hx.2.2

/-! ## Variational characterization -/

/-- Total disagreement of a proposed boundary state with three observations. -/
def tripleBoundaryCost {d m : ℕ} (p q r x : AntitoneProfile d m) : ℕ :=
  boundaryDistanceNat p x + boundaryDistanceNat q x + boundaryDistanceNat r x

/-- The intrinsic median is a global minimizer of total boundary disagreement.
This gives CAG a canonical robust consensus/denoising operation derived only
from causal order and cell volume. -/
theorem profileMedian_minimizes_totalDistance {d m : ℕ}
    (p q r x : AntitoneProfile d m) :
    tripleBoundaryCost p q r (profileMedian p q r) ≤
      tripleBoundaryCost p q r x := by
  have hpqμ := profileMedian_on_geodesic_pq p q r
  have hqrμ := profileMedian_on_geodesic_qr p q r
  have hrpμ := profileMedian_on_geodesic_rp p q r
  have hpqx := boundaryDistanceNat_triangle p x q
  have hqrx := boundaryDistanceNat_triangle q x r
  have hrpx := boundaryDistanceNat_triangle r x p
  rw [boundaryDistanceNat_comm (profileMedian p q r) q] at hpqμ
  rw [boundaryDistanceNat_comm (profileMedian p q r) r] at hqrμ
  rw [boundaryDistanceNat_comm (profileMedian p q r) p] at hrpμ
  rw [boundaryDistanceNat_comm x q] at hpqx
  rw [boundaryDistanceNat_comm x r] at hqrx
  rw [boundaryDistanceNat_comm x p] at hrpx
  unfold tripleBoundaryCost
  omega

end
end CausalAlgebraicGeometry.CAGMedianGeometry
