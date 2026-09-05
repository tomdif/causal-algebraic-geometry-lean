# Compatibility entropy: testing the proposed gravitational connection

## Outcome

Continuation: [the ordering-cluster investigation](OrderingClusterProgress.md)
now gives an exact connected-region representation of the residual cost,
locally generated ownership constraints, and mean-cluster bounds. The full
area law remains open.

The experiment gives a mathematical reduction and a caution, not a derivation
of gravity. The compatibility deficit splits into two nonnegative parts.
The height-trimming part has a proved codimension-two upper bound. The
remaining weak-ordering part is the unresolved obstruction to a full area
upper bound. Small four-dimensional boxes are consistent with area scaling,
but most of their deficit comes from the imposed height ranges.

No claim of literature novelty is made. The strict-to-weak bijection was
already proved in `C3OrderIdealReduction.lean` and is reused here.

## Exact definitions and proved statements

Use ambient dimension `j = d+1`, box side `m >= 1`, and natural logarithms:

- `D = D_j(m)` counts ideals of `[m]^j`, equivalently antitone profiles
  on `[m]^d` with heights in `{0,...,m}`.
- `H = H_j(m)` counts profiles on the SAME base, with heights in
  `{0,...,m-1}`. Only the height factor is shortened, not the whole box.
- `Q = Q_d(m)` counts pairs `phi < psi` at every base point, with both
  profiles in the original height range.

Subtracting one from `psi` identifies strict pairs with weakly ordered
pairs in the H-profile space. In order-ideal notation, these are ideals of
`[m]^d x [m-1] x [2]`. The strict-to-weak profile equivalence is checked in
Lean; the rectangular subgraph encoding is also used by the Python experiment.

Define

```
Delta = 2 log D - log Q = -log(Q/D^2)
T     = 2 log(D/H)             (height-trimming cost)
W     = log(H^2/Q)             (weak-ordering cost).
```

`Q/D^2` is the success fraction for two independent uniform profiles. The
constraints `phi <= m-1` and `psi >= 1` first contribute `(H/D)^2`;
conditional on them, weak ordering after the shift contributes `Q/H^2`.
This is compatibility surprisal, not automatically Shannon mutual information,
thermodynamic entropy, or quantum entanglement entropy. Lean formalizes the
finite cardinality ratios and logarithms, not a measure-theoretic KL bridge.

`CAGCompatibilityEntropy.lean` proves

```
0 < Q/D^2 <= 1,
Q <= H^2 <= D^2,
D <= H * D_d(m),
Delta = T + W,
0 <= T <= 2 log D_d(m),
0 <= W.
```

The key new counting inequality lowers every positive height by one and
records the occupied base downset. From these two pieces, the original
profile is recovered: `h = (h-1) + min(h,1)` using truncated natural
subtraction. Hence at most one base-downset choice is lost per trimmed
profile. The dimension law then gives, for `j = r+3`,

```
T <= 2*m^(r+1)*log 16.
```

In particular, **`T_4(m) <= 2*m^2*log 16`**. Because both costs are
nonnegative, Lean also proves the exact reduction

```
Delta_4(m) has a uniform O(m^2) upper bound
    iff
W_4(m) has a uniform O(m^2) upper bound.
```

Here the precise predicate requires a nonnegative constant and the bound
for every positive integer `m`. This is not a matching lower bound, a limit
theorem, or a proof that either open predicate holds. The existing weaker
`Delta_4 = O(m^(5/2))` bound remains the unconditional bound for the total.

The stronger proposed target

```
Delta_4(m)/m^2 -> sigma,  sigma > 0
```

is explicitly declared as `CompatibilityAreaLawFour : Prop`. It is not
introduced as an axiom and is not asserted by any theorem.

## Exact finite results

Run the dependency-free experiment and its separate tests:

```sh
python3 scripts/compatibility_entropy_probe.py
python3 scripts/compatibility_entropy_probe.py --dimension 3 --max-side 5
python3 -m unittest discover -s scripts -p test_compatibility_entropy_probe.py -v
```

Four-dimensional counts:

| Side m | D | H | Q | Delta/m^2 | T/m^2 | W/m^2 |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 1 | 1 | 1.386294 | 1.386294 | 0 |
| 2 | 168 | 20 | 168 | 1.280991 | 1.064116 | 0.216875 |
| 3 | 17,792,748 | 211,250 | 4,142,605,276 | 1.249335 | 0.985223 | 0.264112 |

At `m=3`, the total deficit is `11.244012`, of which `8.867008`, about
79%, is trimming and `2.377004` is ordering. The compatibility probability
is approximately `1.3085415e-5`.

Three-dimensional control:

| Side m | Delta/m | T/m | W/m |
|---:|---:|---:|---:|
| 1 | 1.386294 | 1.386294 | 0 |
| 2 | 1.497866 | 1.203973 | 0.293893 |
| 3 | 1.564578 | 1.148511 | 0.416067 |
| 4 | 1.601317 | 1.121872 | 0.479444 |
| 5 | 1.621691 | 1.106248 | 0.515443 |

The state counts are exact arbitrary-precision integers; the logarithms
are floating-point evaluations. A slice is an ideal in one fewer chain
factor, and a box is counted as a decreasing chain of such slices. For
chain length three the count is the sum, over middle states, of the
number of predecessors times the number of successors. The largest default
calculation uses 8,790 transfer states.

The tests independently enumerate all subsets in small boxes, enumerate
all short transfer chains, and compare the shifted-pair count against
direct strict comparisons of actual height profiles. They check the
three-dimensional plane-partition counts against the MacMahon product.
These computations are NOT Lean numerical certificates. No asymptotic
regression or extrapolated coefficient is reported. Three four-dimensional
points cannot distinguish `m^2` from alternatives with slow corrections.

As a lower-dimensional warning, the classical rectangular plane-partition
product gives `D_2(m)^2/Q_1(m) = 2(m+1)`, so `Delta_2(m) = log(2(m+1))`,
not a constant at the naive `m^0` scale. The script checks this identity
for its finite two-dimensional cases; its all-m combinatorial derivation
is not formalized here. Thus a universal pure-power area statement across
all dimensions would be incorrect.

## What this says about gravity

An area-like counting term can result from restrictive boundary conditions.
Its exponent alone does not identify a horizon entropy or a gravitational
interaction. Our interpretation of the finite data is therefore more
cautious than simply assigning the whole deficit to gravity.

[Jacobson's thermodynamic derivation](https://arxiv.org/abs/gr-qc/9504004)
uses entropy proportional to horizon area AND the local heat/temperature
relation for Rindler horizons, with energy flux and Unruh temperature.
Those structures are not supplied by this counting experiment.
[Verlinde's entropic-gravity proposal](https://arxiv.org/abs/1001.0785)
likewise makes additional assumptions about emergent space and the role
of matter; it does not turn an arbitrary entropy deficit into gravity.

Even if the area-law target were proved, the next necessary work would be:

1. A local boundary interpretation of the ordering cost, including its
   behavior under refinement and changes in outer boundary conditions.
2. A specified source-constrained ensemble, a notion of source separation,
   and a subtraction of the unconstrained and single-source costs.
3. A derived interaction law and continuum geometry, with checks of its
   sign, range, and dependence on the source model.

The current experiment has no source-separation parameter or temperature,
and the coordinatewise order on a grid is not automatically a physical
Lorentzian causal order. It yields neither attraction, an inverse-square
force, Newton's constant, nor Einstein's equations. Existing discrete
Poisson results from an assumed Dirichlet energy do not fill this gap.

The immediate mathematical target is now precise: control
`W_4(m) = log(H_4(m)^2/Q_3(m))` at area scale, then test whether the surviving
term is local and robust under boundary-condition changes.

## Verification surface

The full default `lake build` passes (3,486 jobs), and all six Python tests
pass. Existing unrelated Lean linter warnings remain unchanged.

The three new `FinalCheck` endpoints audit the surprisal decomposition,
the height-trimming area bound, and the equivalence of open area-upper-bound
targets. Their guarded axiom reports allow only `propext`, `Classical.choice`,
and `Quot.sound`. The full area-law predicate is not a checked conclusion.
