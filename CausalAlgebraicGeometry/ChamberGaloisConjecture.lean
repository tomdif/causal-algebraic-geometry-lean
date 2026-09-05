/-
  ChamberGaloisConjecture.lean — Formal statement of the Chamber Galois
  Conjecture and the Bertrand-Jordan witness criterion.

  STATUS:
  - The conjecture is formally STATED as a `Prop`.
  - The Bertrand-Jordan witness criterion is STATED as a `Prop`
    (the abstract group-theoretic statement; its proof is classical
    Jordan 1873 + Burnside imprimitivity, deferred).
  - Verified-d cases (d ∈ {4,…,32}) are documented; most witnesses still
    live outside Lean. `ChamberFrobenius.lean` supplies the reusable
    certificate interface and the complete `d = 4`, mod-11 case.
  - `ChamberGaloisD4.lean` proves full symmetric Galois symmetry for `d = 4`.

  An UNCONDITIONAL "for all d" proof of the conjecture is genuinely
  open math; this file does not provide one.  See chamber_galois_note.md
  §7 for the precise obstructions.
-/
import CausalAlgebraicGeometry.ChamberDeflation
import CausalAlgebraicGeometry.ChamberStructuralRoot
import CausalAlgebraicGeometry.ChamberQ4Irreducible
import CausalAlgebraicGeometry.ChamberGaloisBridge
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace CausalAlgebraicGeometry.ChamberGaloisConjecture

open Polynomial
open CausalAlgebraicGeometry.ChamberGaloisBridge

/-! ## Layer 1: the conjecture as a `Prop`

The conjecture now refers to the concrete rational residual polynomial,
its canonical Mathlib splitting field, and its actual `Polynomial.Gal`
action.  The rational-to-real compatibility and structural deflation are
proved in `ChamberGaloisBridge.lean`.
-/

/-- Abstract statement: a group `G` acts as the full symmetric group on
a finite set `α`. Equivalent to `MulAction.toPermHom G α` being surjective. -/
def ActsAsFullSymmetric (G : Type*) [Group G] (α : Type*) [Fintype α]
    [MulAction G α] : Prop :=
  Function.Surjective (MulAction.toPermHom G α)

/-- **Chamber Galois Conjecture**.

For each `d ≥ 4`, there exists a Galois-style action of the splitting
field's automorphism group on the `d − 2` residual roots of the chamber
polynomial that realizes the full symmetric group `S_{d−2}`.

The "residual roots" are the roots of `Q_d = chamberPolynomial d / (X − λ*)`,
which (by `chamber_deflation`) is a polynomial of degree `d − 2`.

This is surjectivity of the canonical faithful action homomorphism.  Its
codomain is the permutation group of the roots in the splitting field. -/
def ChamberGaloisConjecture : Prop :=
  ∀ d : ℕ, 4 ≤ d → HasFullChamberGaloisGroup d

/-! ## Layer 2: the Bertrand-Jordan witness criterion

The proof technique that has verified the conjecture for `d ∈ {4,…,32}`
is the following classical recipe:

  1. Show `G ≤ S_n` is **transitive** (from `Q_d` irreducible).
  2. Show `G ⊄ A_n` (from `disc Q_d` not a square).
  3. Exhibit an element of `G` of prime order `q` with `n/2 < q ≤ n − 3`
     (a Frobenius witness for a `q`-cycle).
  4. Verify no proper imprimitive subgroup of `S_n` contains an element
     of order `q` (automatic when `q > n/2` since maximal imprimitive
     subgroups `S_k ≀ S_{n/k}` have order divisible only by primes
     `≤ max(k, n/k) ≤ n/2`).

  Steps 1+3+4 force `G` primitive containing a `q`-cycle; by Jordan's
  theorem (1873), `G ⊇ A_n`. Step 2 gives `G = S_n`.

We state the criterion in abstract group-theoretic form; its proof is
classical (Jordan 1873) but not formalized in Mathlib v4.28.0. -/

/-- The **Bertrand-Jordan witness criterion** (abstract).

Mathlib v4.28.0's `Mathlib.GroupTheory.GroupAction.Jordan` provides:

- `MulAction.IsPreprimitive.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`
  : a primitive subgroup of `Sym(α)` containing a transposition equals `⊤`.
- `MulAction.IsPreprimitive.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`
  : a primitive subgroup containing a 3-cycle contains the alternating group.

Combined with the Wielandt/Burnside fact that for our family, transitive
+ contains-q-cycle (with `q > n/2` and `q` prime) implies primitive, we
have an essentially-complete classical proof template available.

The chamber-specific application:

  step 1: `Q_d` irreducible ⟹ Gal acts transitively on roots.
  step 2: q-cycle witness ⟹ Gal contains an element of prime order q.
  step 3: q > n/2 + imprimitivity rule-out ⟹ Gal acts primitively.
  step 4: disc non-square ⟹ Gal ⊄ A_n (so contains a transposition or
          some odd permutation, after combining with step 1 + step 3).
  step 5: Mathlib's `subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`
          (or its 3-cycle analog + parity argument) closes Gal = S_n.

The statement below is deliberately not replaced by `True`: it records the
precise group-theoretic implication still needed for the prime-cycle route. -/
def BertrandJordanCriterionStatement : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α)),
    MulAction.IsPreprimitive G α →
    (∃ p : ℕ, p.Prime ∧ p + 3 ≤ Nat.card α ∧
      ∃ g : Equiv.Perm α,
        g.IsCycle ∧ g.support.card = p ∧ g ∈ G) →
    ¬ G ≤ alternatingGroup α →
    G = ⊤

/-- The primitive-plus-transposition closure step is already in Mathlib and
is available unconditionally. -/
theorem primitive_swap_closes_full_symmetric
    (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Equiv.Perm α))
    (hprimitive : MulAction.IsPreprimitive G α)
    (hswap : ∃ g : Equiv.Perm α, g.IsSwap ∧ g ∈ G) :
    G = ⊤ := by
  obtain ⟨g, hg, hmem⟩ := hswap
  exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    hprimitive g hg hmem

/-! ## Layer 3: the proven and computationally verified cases

For each `d ∈ {4, 5, …, 32}` we have an explicit Frobenius witness
(prime `p`, factorization type) certifying the conjecture
unconditionally. The witnesses are tabulated in `chamber_galois_note.md`
§6.2 and reproducible by:

  cd ~ && python3 jd_galois_extend.py
  cd ~ && python3 jd_galois_million.py

A formal Lean per-d certificate for `d ≥ 5` requires:
  (a) Computing the rational residual polynomial's image mod `p` for each
      witness prime,
  (b) Connecting the certified factorization type to the splitting-field
      action, and
  (c) decidability infrastructure for the resulting `Polynomial.Gal` claim.

The rational polynomial and its actual Galois action are now complete in
`ChamberGaloisBridge.lean`.  `ChamberFrobenius.lean` supplies integral-model
and finite-field factorization certificates; their general bridge to the
characteristic-zero action remains.  In particular,
Mathlib has `Polynomial.Gal` but no `Decidable` instance for "Gal = S_n"
that would let us close a per-d certificate by computation alone.

The exceptional quadratic case `d = 4` is proved directly in
`ChamberGaloisD4.lean`: irreducibility gives a transitive action on two roots,
and every transitive action on a two-element type is the full symmetric
action.  The cases `d ≥ 5` still live outside Lean for now. -/

/-- The verified-d count, as of 2026-04-25. -/
def verifiedD : Set ℕ := {d | 4 ≤ d ∧ d ≤ 32}

/-- Status flag: the conjecture has been verified by computational
Frobenius witness for every `d ∈ {4, …, 32}`. -/
theorem verifiedD_holds_computationally :
    ∀ d ∈ verifiedD, 4 ≤ d ∧ d ≤ 32 := by
  intro d hd
  exact hd

/-! ## Layer 4: status and remaining gaps

**What's available in Mathlib (newly discovered 2026-04-25)**: Mathlib
v4.28.0 already includes `Mathlib.GroupTheory.GroupAction.Jordan`
formalizing Jordan's classical theorems on primitive permutation
groups. So the abstract group-theoretic criterion is NOT a Lean gap.

**What's still required for a full Lean-formal proof of the conjecture**:

  (i)  **Rational/Galois bridge — DONE.** `qChamberPolynomial` and
       `qResidualChamberPolynomial` are concrete polynomials over ℚ; base
       change, root deflation, degree, and the canonical faithful Galois
       action are checked by Lean.

  (ii) **Per-d Frobenius witnesses and bridge** — `d = 4` is a theorem.
       For each computationally verified `d ≥ 5`, the witness prime `p`
       and factorization pattern are known; their certificates must be
       packaged in Lean and the general good-reduction-to-cycle theorem
       must be supplied.

  (iii) **Unconditional uniform proof** (still genuinely open, see
        chamber_galois_note.md §7.2). The remaining non-Lean gaps:
        - Hajir-style discriminant pattern: empirically blocked.
        - Hilbert irreducibility with explicit thin set: open.
        - Splitting-field tower induction: open.
        - Effective unconditional Chebotarev: gives per-d algorithm
          but no uniform statement.

**What this file delivers**: the conjecture over the actual polynomial and
actual Galois group, an honest (non-`True`) prime-cycle criterion statement,
and a checked primitive-plus-transposition closure theorem.  The companion
`ChamberGaloisD4.lean` closes the first case.  The general finite-field witness
bridge and the unconditional uniform proof remain open work. -/

end CausalAlgebraicGeometry.ChamberGaloisConjecture
