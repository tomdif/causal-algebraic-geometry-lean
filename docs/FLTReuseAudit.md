# FLT formalization reuse audit

Reference examined: Anthropic's `fermats-last-theorem` repository.

## Adopted

- A compact final-check module with stable, challenge-facing theorem names.
- Pinned kernel dependency reports using `#guard_msgs` and `#print axioms`.
- A proof-path document that distinguishes theorem endpoints from conditional
  inputs and conjectures.
- Use of Mathlib's concrete `Polynomial.Gal`, splitting-field, root-action,
  topology, and sheaf interfaces instead of informal stand-ins.

## Extracted locally

No FLT source module was copied or imported.  CAG now contains a set of small,
project-specific bridges:

- `CSpecActualSheaf.lean`: a generated topology and genuine sheaf on CSpec.
- `CSpecRingSheaf.lean`: the genuine noncommutative ring-valued refinement.
- `ChamberGaloisBridge.lean`: the rational chamber recurrence, exact base
  change, deflation, and canonical Galois action.
- `ChamberGenericFamily.lean`: a parameterized family and its generic member
  over the rational-function field.
- `ChamberFrobenius.lean`: integral models, finite-field factor certificates,
  and a complete `d = 4`, mod-11 seed.
- `ChamberGaloisD4.lean`: full `S₂` chamber symmetry and an actual two-cycle
  for `d = 4`.
- `CSpecChamberRoots.lean`: the chamber-root sheaf and local faithful Galois
  actions over the causal spectrum, with fixed-dimension constancy.
- `CSpecChamberRootsCounterexample.lean`: a formal disproof of unrestricted
  root-sheaf local constancy.

These modules reuse public Mathlib APIs and CAG's own definitions.  Their
scope is narrow enough for line-by-line review.

## Not adopted

- No direct Lake dependency on the FLT repository.  FLT is pinned to
  Lean/Mathlib v4.33.x while CAG is pinned to v4.28.0; a dependency would
  couple unrelated toolchains and import a very large proof graph.
- No FLT-specific Mazur, Ribet, modularity-lifting, or Langlands--Tunnell
  theorem is relevant to the current CAG conjectures.
- No claim is inferred merely from FLT's repository-level self-assessment.
  CAG's local kernel checks remain the authority for CAG endpoints.

## Remaining reusable layer

Finite-field reduction and squarefree factorization patterns now have a
reusable Lean certificate interface.  The next theorem is the general
good-reduction bridge connecting a certificate's nontrivial factor degrees
to `cycleType` in `chamberGaloisActionHom`; degree-one factors are fixed points
and therefore absent from Mathlib's cycle type.  The quadratic `d = 4` result
is already proved directly.  After the general bridge, the external per-d
witness table can be ported incrementally without importing the FLT
development wholesale.
