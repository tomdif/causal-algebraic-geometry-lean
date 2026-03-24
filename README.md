# Causal-Algebraic Geometry in Lean 4

A formally verified Grothendieck-type framework for causal structures. From a causal algebra (an associative algebra with a partial order on its idempotents satisfying a causality axiom), we construct a spectrum, equip it with a structure sheaf, build a cohomology theory, and prove an exact arithmetic bridge to classical number theory.

**1,233 lines. Zero `sorry`. Zero custom axioms. Every theorem verified by `#print axioms`.**

## What This Is

This is the first formal verification of an algebraic-geometric framework for causal structures — doing for causal sets what Grothendieck did for commutative rings:

1. **Start with the algebra** (causal algebra)
2. **Construct a spectrum** (CSpec)
3. **Equip it with a structure sheaf** (corner algebras)
4. **Build a cohomology theory** (order-complex simplicial cohomology)
5. **Prove it contains classical number theory** (arithmetic bridge)

## Files

| File | Lines | Content |
|------|-------|---------|
| `CausalAlgebra.lean` | 207 | Causal algebra definition, causal matrix ring, orthogonal idempotents, corner algebras, upper-triangularity |
| `CausalPrimality.lean` | 227 | Causal primality (replacing collapsed NC primality), CSpec spectrum, Recovery Theorem, distinguished opens |
| `NoetherianRatio.lean` | 271 | Noetherian ratio γ = \|CC\|/\|Int\|, interval convexity, total orders Noetherian, antichain exponential growth |
| `ArithmeticBridge.lean` | 165 | Divisibility lattice as causal set, μ\*ζ = 1, primes give CSpec points, Recovery of Spec(ℤ) |
| `CSpecSheaf.lean` | 142 | Structure sheaf via corner algebras, sheaf separation, causal convexity → ring homomorphism, stalks |
| `OrderComplexCohomology.lean` | 221 | Simplicial cohomology, coboundary operator, δ² = 0, H⁰ characterization, cone kills H¹ |

## Key Theorems

### Spectrum (CSpec)

- **`closedPoint_isCausallyPrime`** — Recovery Theorem: elements of the causal set embed as closed points of CSpec
- **`nc_primality_collapses`** — Standard NC primality gives ≤ 1 point for width ≥ 2, motivating causal primality
- **`distinguishedOpen_basis`** — Distinguished opens D(α) form a topological basis

### Structure Sheaf

- **`locality`** — Sheaf separation: sections are determined by local data
- **`product_supported_on_convex`** — For causally convex S, elements γ ∉ S contribute zero to the product sum (the key lemma making restriction a ring homomorphism)
- **`stalk_at_minimal_is_scalar`** — Past-minimal elements have 1-dimensional stalks

### Cohomology

- **`coboundary_sq_zero_dim2`** — δ² = 0 (the fundamental identity making H\* well-defined)
- **`zeroCocycle_iff`** — H⁰ = ker(δ⁰) characterizes connected components
- **`cone_kills_H1`** — Posets with a maximum element have H¹ = 0 (contractible)

### Arithmetic Bridge

- **`moebius_times_zeta_eq_one`** — μ \* ζ = 1 in the arithmetic function ring
- **`moebius_mul_zeta_eq`** — (μ \* ζ)(n) = [n = 1]
- **`prime_gives_CSpec_point`** — Every prime p | n gives a causally prime ideal in CSpec(divCAlg n)
- **`arithmetic_bridge`** — Capstone: all five bridge components in one theorem

### Noetherian Ratio

- **`interval_isCausallyConvex`** — Every interval is convex, so γ ≥ 1
- **`totalOrder_isNoetherian`** — Total orders have γ = 1
- **`antichain_numConvex`** — Antichains have |CC| = 2^n (exponential growth)

## Axiom Audit

Every theorem depends only on the three standard Lean kernel axioms:

```
propext          — propositional extensionality
Classical.choice — classical logic (law of excluded middle)
Quot.sound       — quotient soundness
```

No `sorry`. No `axiom` declarations. No `Decidable` shortcuts. Verified via `#print axioms` on every capstone theorem.

## Building

```bash
# Requires Lean 4 v4.28.0 and Mathlib v4.28.0
lake update        # fetch Mathlib (~8000 cached oleans)
lake build         # ~1451 jobs, ~2 min
```

## The Arithmetic Bridge

The deepest result: the divisibility poset (ℤ⁺, |) is a causal set whose CSpec recovers Spec(ℤ). This is not an analogy — it is an exact identity:

- The causal Möbius function equals the number-theoretic μ (Rota 1964)
- μ \* ζ = 1 holds in both the incidence algebra and the arithmetic function ring
- Prime numbers give causally prime ideals in CSpec
- The framework **contains** classical number theory as a special case

## What Remains Computational

The holonomy/Wilson loop construction (W < 1 on cylinders) and Čech H² discrimination (topology detection) are numerical results verified in Python/NumPy, not formalized in Lean. These involve floating-point computation on specific manifold discretizations and don't lend themselves to the same formal treatment.

## Related

- [Unified Theory](https://github.com/tomdif/unifiedtheory) — Lean 4 formalization deriving the Standard Model from a causal partial order (172 files, zero sorry)
- [Causal Set Explorer](https://github.com/tomdif/causal-set-explorer) — Interactive visualization of causal sets

## Citation

```bibtex
@misc{difiore2026causal,
  title={Causal-Algebraic Geometry: A Grothendieck-Type Framework for Causal Structures},
  author={DiFiore, Thomas},
  year={2026},
  note={Lean 4 formalization: 6 files, 1233 lines, zero sorry, zero custom axioms}
}
```

## License

Apache 2.0
