# CAG causal-state geometry: proved core and effective physics

## Outcome

The repository now contains a genuine geometry on both the boundary degrees
of freedom selected by the `c₃` counting theorem and the downset states of an
arbitrary finite causal algebra. It has fifteen layers with different logical
status.

| Layer | Object | Status |
|---|---|---|
| State metric | L¹ height distance between antitone profiles | Proved in Lean |
| General causal-state metric | Event symmetric-difference/Hamming distance on downsets of any finite causal poset or `CAlg` | Proved in Lean |
| Median/lattice geometry | Bounded distributive lattice, valuation metric, unique three-state median | Proved in Lean |
| Transition/cubical geometry | Hasse graph, exact shortest paths, median graph, explicit partial-cube embedding | Proved in Lean |
| Grid extrinsic curvature | Mixed plaquette Hessian of the height graph | Proved in Lean |
| Intrinsic cubical curvature | Two-direction square obstruction and total local square-completion defect | Proved in Lean |
| Higher cubical complex | Event hyperplanes, isometric Boolean cubes, cubical faces, links, and link Laplacian | Proved in Lean |
| Directional frontier geometry | Complete event-labeled tangent frame, directional Laplacian trace, exact order-indicator sectional kernel, and full ordered curvature trace | Proved in Lean |
| Discrete connection and fiber metric | Partial event-wall parallel transport, flat composition/holonomy laws, positive-definite directional metric, and covariant differences | Proved in Lean |
| Functoriality and causal refinement | Full invariance under order isomorphism; isometric growth and old-frame injection under past-closed embeddings; exact new-direction count | Proved in Lean |
| Infinite refinement control | Exact cumulative degree law, linear-growth/stabilization criteria, and normalized curvature-density bound | Proved in Lean |
| Refinement-limit compactness | Unconditional convergent curvature subsequence; full curvature-density and persistent-field convergence under summable variation, with tail bounds | Proved in Lean |
| Controlled continuum scaling | Product smooth fields and arbitrary-poset radial fields | Proved in Lean: coupled coordinate-smooth product limit, exact nonproduct birth–death operator, and branching-controlled drift–diffusion expansion |
| Field equation | Graph Poisson equation from nearest-neighbor Dirichlet action, including arbitrary finite causal-state graphs | Proved from an explicit effective-action hypothesis |
| Spectral prediction | `ω²=(c/a)²4sin²(q/2)` | Exact consequence of that effective model; physical only after independent scale/field identification |

## Metric

For boundary profiles `p,q : [m]^d → {0,...,m}` define

```text
d₁(p,q) = Σ_x |p(x)-q(x)|.
```

`CAGBoundaryGeometry.lean` proves identity of indiscernibles, symmetry, and
the triangle inequality. Combinatorially, this is exactly the number of
vertical cells in the symmetric difference of the two subgraphs. It is an
intrinsic metric on CAG boundary states, not a claimed Lorentzian interval on
the event poset.

## Distributive-lattice and median geometry

`CAGMedianGeometry.lean` proves that pointwise intersection and union keep a
height profile antitone. Consequently the finite boundary state space is a
bounded distributive lattice. If

```text
Vol(p) = Σ_x p(x),
```

then volume is a lattice valuation and the metric has the exact rank formula

```text
d₁(p,q) = Vol(p ∨ q) - Vol(p ∧ q).
```

The majority profile

```text
med(p,q,r) = (p ∧ q) ∨ (q ∧ r) ∨ (r ∧ p)
```

is proved to be the unique state lying simultaneously on metric intervals
between all three pairs. The same state globally minimizes

```text
d₁(p,x) + d₁(q,x) + d₁(r,x).
```

This is an assumption-free median metric geometry derived from causal order
and cell counting. It supplies exact interpolation, consensus, and robust
aggregation operations for boundary data. It is substantially stronger than
having an arbitrary distance formula, but remains a geometry of boundary
states rather than an event-level Lorentzian geometry.

## Transition graph and partial cube

`CAGTransitionGeometry.lean` turns the integer metric into a concrete local
geometry. Two states are adjacent exactly when one admissible unit cell is
added or removed. The development proves:

```text
adjacent(p,q) ↔ p covers q or q covers p,
graphDistance(p,q) = d₁(p,q).
```

The proof is constructive. For `p<q`, choose a minimal base point at which
their heights differ and raise `p` there by one. Minimality guarantees that
the new profile remains antitone. Iterating and routing through `p∧q` gives a
shortest one-cell walk between arbitrary states.

The resulting connected graph has a unique graph median for every triple.
Moreover, the binary occupancy code

```text
code(p)(x,z) = [z < p(x)]
```

is injective and satisfies

```text
graphDistance(p,q) = HammingDistance(code(p),code(q)).
```

This is an explicit partial-cube realization, rather than an appeal to the
external theorem that median graphs are partial cubes. Each causal unit cell
therefore defines a binary wall, and distance counts exactly the walls that
separate two boundary states.

## Arbitrary finite causal posets and causal algebras

`CAGFiniteCausalGeometry.lean` removes the rectangular grid from the median
and partial-cube construction. For a finite causal poset `P`, a state is a
lower set `S ⊆ P`, with event-occupancy code

```text
code(S)(a) = [a ∈ S].
```

The file proves, without a grid hypothesis,

```text
d(S,T) = |S △ T| = HammingDistance(code(S),code(T)),
adjacent(S,T) ↔ S covers T or T covers S,
graphDistance(S,T) = d(S,T),
med(S,T,U) = (S∩T) ∪ (T∩U) ∪ (U∩S).
```

The median is the unique common point of the three pairwise metric intervals.
The graph is connected, median, and isometrically embedded in the Boolean
cube indexed by causal events. A wrapper installs the internal order of any
finite `CAlg`, and `causalDownsetEquiv` proves that these bundled states are
equivalent to the repository's original predicate-based `IsDownset` notion.
Thus the result now applies to arbitrary finite causal algebras, not only the
`c₃` grid boundary sector.

This is a metric on causal *states* (consistent event histories). It is not a
Lorentzian interval between individual events.

## Grid plaquette curvature

For an integer height field `h`, a cell `x`, and coordinate directions `i,j`,
define

```text
K_ij(x) = h(x+e_i+e_j)-h(x+e_i)-h(x+e_j)+h(x).
```

The Lean development constructs the boundary-safe grid maps, defines this
tensor, and proves `K_ij=K_ji` and zero curvature for constant height fields.
This is discrete mixed/extrinsic curvature of a graph surface. It is not yet a
Riemann tensor with connection, contractions, or a Lorentzian signature.

## Intrinsic cubical curvature obstruction

The generic state graph also supports a coordinate-free local invariant. For
a vertex `v` and two distinct neighboring states `a,b`, define

```text
κ_v(a,b) = 0  if the two moves complete to a nondegenerate square,
           1  otherwise.
```

`cubicalSectionalDefect` is this symmetric two-direction kernel, and
`squareCompletionDefect` counts all ordered incident pairs with value one.
The Lean development proves:

- symmetry in the two directions and zero diagonal;
- total defect zero exactly when every incident move-pair completes to a
  square;
- any exhibited noncommuting pair forces positive total defect;
- the middle state of the three-state graph belonging to a two-event causal
  chain has strictly positive defect.

This is intrinsic because it uses only graph adjacency. It detects local
causal precedence as failure of independent moves to commute. It is a
rigorous discrete sectional obstruction, but it is not claimed to be a
multilinear Riemann tensor, Ricci curvature, or a continuum curvature scalar.

## Higher cubical complex, hyperplanes, and links

`CAGCubicalComplex.lean` promotes the partial-cube graph to explicit
higher-dimensional cells. Each causal event `a` defines a canonical wall
according to whether `a` belongs to a downset. The development proves

```text
graphDistance(S,T)
  = number of event walls separating S and T,
```

and every transition edge crosses a unique event wall.

An event is addable at `S` when it is absent and every strict predecessor is
already present. A `CausalCube` consists of a base state and a finite family
`D` of events all addable there. The directions are proved pairwise
incomparable. Every subset `A ⊆ D` gives the vertex `S ∪ A`, and Lean proves

```text
distance(S∪A,S∪B) = |A △ B|.
```

Thus the vertex map is injective and isometric, and two cube vertices are
adjacent exactly when their direction subsets differ in one coordinate.
Restriction and upper-face constructions prove closure under Boolean faces.
Every two distinct cube directions generate a certified transition square.

The cubical link at a state has incident transitions as vertices and joins
two precisely when they complete to a nondegenerate square. The earlier total
curvature defect vanishes exactly when this link is complete. Cube directions
embed injectively as a clique in the link. Finally, `cubicalLinkLaplacian`
defines an intrinsic operator on local commuting directions and annihilates
constant link fields.

## Controlled causal-chain scaling limit

`CAGScalingLimit.lean` supplies the first rigorous bridge from a growing CAG
family to a continuum differential operator. For the total order on `n`
events, every downset is proved to be a unique prefix containing `k` events.
Consequently,

```text
Downsets(chain n) ≃ {0,...,n},
d(S_k,S_l) = |k-l|,
stateGraph(chain n) ≃ pathGraph(n+1).
```

At an interior state, the intrinsic CAG graph Laplacian is exactly

```text
(Δ_G φ)(k) = 2φ(k)-φ(k-1)-φ(k+1).
```

A physical spacing `h` is then supplied explicitly, giving coordinate
`x_k=hk`. Sampling a continuum field `f` on the chain proves

```text
h⁻² Δ_G f(x_k)
  = [2f(x_k)-f(x_k-h)-f(x_k+h)]/h².
```

For a general quartic field with leading coefficient `A`, Lean proves the
exact consistency formula

```text
h⁻² Δ_G f(x_k) = -f''(x_k) - 2Ah²,
|h⁻² Δ_G f(x_k)+f''(x_k)| = 2|A|h².
```

This error is uniform in chain length and interior position. For an
independently specified physical interval length `L`, the development sets
`h_n=L/n`, proves the terminal state lies at `L`, proves `h_n→0`, and proves
the certified error tends to zero.

This is a genuine operator-consistency and convergence theorem for one
controlled family. The causal order does not determine `L`; choosing the
physical length remains external.

## Controlled two-dimensional scaling and causal Hessian

`CAGTwoDimensionalLimit.lean` advances the construction from a line to a
genuine causal rectangle. Its event poset is the disjoint sum of chains of
lengths `n` and `m`. Lean proves that every downset is uniquely a pair of
prefixes and consequently

```text
Downsets(chain n ⊕ chain m) ≃ {0,...,n} × {0,...,m},
d(S_(i,j),S_(k,l)) = |i-k| + |j-l|,
stateGraph(chain n ⊕ chain m)
  ≃ pathGraph(n+1) □ pathGraph(m+1).
```

The grid therefore arises from the causal order itself. At every interior
state its intrinsic graph Laplacian is exactly the five-point operator

```text
(Δ_G φ)(i,j)
  = 4φ(i,j)-φ(i-1,j)-φ(i+1,j)-φ(i,j-1)-φ(i,j+1).
```

For a coupled quartic surface containing independent quartic and cubic terms,
the nonseparable term `x²y²`, and lower terms, the scaled CAG operator obeys

```text
h⁻²Δ_G f = -Δ_Euclidean f - 2(A_x+A_y)h²,
|h⁻²Δ_G f + Δ_Euclidean f| = 2|A_x+A_y|h².
```

The error is uniform in both interior coordinates. On fixed physical squares
with `h_n=L/n`, Lean proves the error tends to zero and the terminal state is
located exactly at `(L,L)`.

`CAGPlaquetteLimit.lean` supplies the mixed-derivative bridge. The next event
in each chain is proved independently addable, so every elementary rectangle
is a certified two-dimensional `CausalCube`. Its two axes form an edge in the
intrinsic cubical link, and its four vertices are the expected four grid
states. The alternating scalar-field sum around that causal square, divided
by `h²`, is proved to equal the continuum mixed derivative `∂ₓ∂ᵧf` at the cell
center for the same coupled quartic class. In particular, the nontrivial
`x²y²` interaction is recovered exactly rather than splitting into two 1D
calculations.

These are controlled product-family results. The physical length `L` and the
Dirichlet effective action remain explicit external inputs, not quantities
derived from microscopic CAG weights.

## Arbitrary-dimensional product scaling

`CAGProductScalingLimit.lean` closes the finite-dimensional product frontier.
For every `d` and `n`, it constructs the causal event poset consisting of `d`
mutually independent `n`-event chains. Its state coordinates and grid graph
are defined recursively, and Lean proves

```text
stateGraph(d independent chains)
  ≃ pathGraph(n+1) □ ... □ pathGraph(n+1),
d_CAG(k,l) = Σ_i |k_i-l_i|.
```

The disjoint-sum theorem behind this result is itself general: the downset
graph of any two causally disconnected finite posets is the box product of
their downset graphs, and event-wall distance splits additively.

Fully interior product coordinates carry two neighbors per axis. Lean proves
that the intrinsic CAG graph Laplacian is exactly the recursive
`(2d+1)`-point stencil. For a separable quartic field whose axis-wise leading
coefficients are `A_i`, the scaled operator satisfies the dimension-uniform
identity

```text
h⁻²Δ_CAG f = -Δ_Euclidean f - 2h² Σ_i A_i,
|h⁻²Δ_CAG f + Δ_Euclidean f| = 2h² |Σ_i A_i|.
```

On fixed physical `d`-cubes with `h_n=L/n`, the terminal causal state is
proved to lie exactly at `(L,...,L)` and the certified uniform error tends to
zero. The theorem holds for every finite `d`; it does not treat dimension as
a hard-coded special case.

`CAGSmoothScalingLimit.lean` removes the quartic and separability restrictions
from the Laplacian comparison. For an arbitrary coupled field
`f : ℝ^d → ℝ`, define the coordinate Laplacian by summing the ordinary
second derivatives of the one-coordinate slices through a point. If each
such slice is globally `C⁴` and its fourth derivative is bounded by `M_i`,
Lean proves at every fully interior state

```text
|h⁻²Δ_CAG f + Δ_coordinate f| ≤ (M₁ + ... + M_d) h² / 12.
```

This is derived from Mathlib's Lagrange-remainder Taylor theorem, including
the reflected left-hand expansion and cancellation of the odd derivatives.
It is uniform over interior states when the slice bounds are uniform, and its
certificate tends to zero on fixed physical cubes with `h_n=L/n`. Mixed
coordinate dependence is allowed; only the causal family itself remains the
flat product of independent chains.

## Arbitrary-poset radial scaling

`CAGNonproductScalingLimit.lean` crosses the first nonproduct frontier. Every
downset state `s` of every finite causal poset has a canonical event-count
rank `r(s)`. Let `d₋(s)` be the number of neighboring states obtained by
deleting one event and `d₊(s)` the number obtained by inserting one event.
For every rank field `F`, Lean proves the exact intrinsic identity

```text
Δ_CAG F(s)
  = d₋(s) [F(r)-F(r-1)] + d₊(s) [F(r)-F(r+1)].
```

Thus a general nonproduct causal order selects a state-dependent birth–death
operator without externally assigned edge weights. Sampling a globally `C⁴`
field at `x=hr` gives the local smooth expansion

```text
h⁻²Δ_CAG f
  = (d₋-d₊) h⁻¹ f'
    - (d₋+d₊)/2 f''
    + (d₋-d₊) h/6 f''' + R,
|R| ≤ (d₋+d₊) M h²/24.
```

At locally balanced states `d₋=d₊`, drift and skew cancel and the
operator converges quadratically to a pure Laplacian with branching
multiplicity. At unbalanced states, a linear test field gives the exact term
`(d₋-d₊)/h`; therefore a finite diffusive continuum limit requires branching
balance, or an explicit renormalization of that drift. A bounded-total-
branching error sequence is proved to converge on fixed domains with
`h_n=L/n`, even when the finite causal poset and state vary with `n`.

The theorem is radial in event-count rank. It does not yet identify a full
multidirectional metric or curvature tensor on arbitrary nonproduct state
spaces, but it isolates the local coefficients and obstruction that such a
limit must control.

## Intrinsic event frame and exact frontier curvature

`CAGDirectionalGeometry.lean` removes the need for product coordinates at
the finite directional level. Every state-graph edge incident to a downset
`S` has a unique event label, distinct edges have distinct labels, and Lean
classifies every incident edge as exactly one of

```text
remove a,  where a is maximal in S,
add b,     where b is absent and all strict predecessors of b lie in S.
```

The graph Laplacian is exactly the trace of the finite differences over this
event-labeled frame. This is a complete intrinsic nonradial frame on each
finite nonproduct state space, although no refinement limit for the whole
frame is claimed yet.

The stronger result is an exact local order-curvature correspondence. For a
removable frontier event `a` and an addable frontier event `b`, the two moves
complete to a nondegenerate graph square if and only if `a ≰ b`. Hence

```text
κ_S(remove a, add b) = 1[a ≤ b].
```

Positive mixed sectional defect therefore reconstructs causal precedence
between the two sides of the active frontier. Summing this kernel proves

```text
total mixed frontier curvature
  = number of causal incidences (a,b) crossing the active frontier.
```

Lean also constructs the joint state reached by any two distinct additions
and by any two distinct removals, proving that all same-sign directional
planes are flat. The frontier labels are bundled into an explicit equivalence

```text
removable frontier ⊕ addable frontier ≃ incident graph directions.
```

Consequently the full ordered trace of the sectional kernel over every graph
direction satisfies the exact scalar identity

```text
K_dir(S) = 2 · #{(a,b) | a removable, b addable, a ≤ b}.
```

The factor two records the two orientations `(remove a, add b)` and
`(add b, remove a)` of each obstructed plane.

This is an exact discrete sectional curvature formula derived only from the
causal order and transition graph. It is not a multilinear Riemann tensor,
and it does not by itself supply a connection, Ricci contraction, or
continuum curvature field.

## Canonical partial discrete connection

`CAGDiscreteConnection.lean` equips the directional fibers with a canonical
transport rule. A direction at `S` is transportable to `T` exactly when its
global event-wall label also occurs in the frame at `T`; its transport is the
unique target direction with that label. This partiality is structural:
causal dependencies can create or destroy frontier directions as the state
changes.

Lean proves exact identity, inverse, and composition laws. Two paths with the
same endpoints transport a persistent direction to the same result, so the
connection has zero holonomy everywhere it is defined. On an actual graph
edge, the edge direction transports to the reverse edge, and reversing twice
returns the original direction.

Each directional fiber is the real vector space

```text
T_S = {X : incident directions at S → ℝ}
```

with event-wall basis metric

```text
⟨X,Y⟩_S = Σ_d X(d)Y(d).
```

The squared norm is nonnegative and vanishes exactly for the zero vector.
Transport preserves the orthonormal basis metric on every common direction.
The covariant finite difference of a directional field is defined by
subtracting its source value from its transported target value; these
differences telescope under composition, while every field depending only on
the global event label is exactly parallel. Finally, the number of event-wall
basis directions is proved equal to the local state-graph degree.

This is a rigorous metric-compatible flat partial discrete connection, not a
continuum Levi-Civita connection. Its flat holonomy is compatible with the
nonzero cubical curvature above: CAG sectional curvature is carried by
failure of two directions to share a square, rather than rotation of labels
around a square that exists.

## Functoriality and genuine causal refinement

`CAGFunctorialGeometry.lean` proves coordinate invariance. Every order
isomorphism of finite causal event posets induces an isometry of their
lower-set state spaces and an isomorphism of transition graphs. Its induced
tangent-frame equivalence preserves the positive-definite norm, commutes with
parallel transport, and preserves every cubical sectional component and the
full directional curvature trace. Thus these constructions depend only on
causal order, not event names or a selected presentation.

`CAGCausalRefinement.lean` then treats genuine growth. A
`PastClosedEmbedding P Q` embeds the old event poset `P` into `Q` while
forbidding new events below old ones. Extending an old downset by retaining
exactly its old events gives

```text
d_Q(extend S, extend T) = d_P(S,T),
adj_Q(extend S, extend T) ↔ adj_P(S,T).
```

Restriction is a left inverse, so extension is injective. Every old tangent
direction injects into the refined frame, retains its event label and
orthonormal metric, and commutes exactly with the canonical connection.
Directions therefore cannot disappear under past-closed growth. Lean defines
the genuinely new directions by the degree difference and proves

```text
degree_Q(extend S) = degree_P(S) + newDirectionCount(S).
```

This is the first formal refinement theorem for CAG geometry. It isolates and
counts the precise local degrees of freedom that a refinement limit must
control.

`CAGRefinementTower.lean` iterates these embeddings. For a compatible state
sequence `S_n`, Lean proves the exact identity

```text
degree(S_n) = degree(S_0) + Σ_{k<n} newDirectionCount(S_k).
```

If at most `B` directions are introduced per step, tangent dimension grows at
most as `degree(S_0)+nB`. If no directions are introduced after some level,
the dimension stabilizes exactly. Independently, the directional curvature
trace satisfies

```text
0 ≤ K_dir(S) ≤ degree(S)²,
0 ≤ K_dir(S)/degree(S)² ≤ 1,
```

with the zero-degree ratio defined as zero. Thus every refinement tower has a
uniformly bounded dimensionless curvature density, and every unnormalized
trace remains even. These bounds provide compactness-style input but do not
by themselves prove that the density converges.

`CAGRefinementConvergence.lean` converts this input into actual limit
theorems. After embedding the rational curvature density in `ℝ`, compactness
of `[0,1]` gives every refinement tower a strictly increasing subsequence and
a limit `L ∈ [0,1]`:

```text
ρ(φ(n)) → L.
```

This subsequential result is unconditional. If the one-step curvature
variation is summable,

```text
Σ_n dist(ρ(n),ρ(n+1)) < ∞,
```

then the entire sequence is Cauchy and converges to a value in `[0,1]`.
Moreover Lean proves the quantitative certificate

```text
dist(ρ(n),L) ≤ Σ_{m≥0} dist(ρ(n+m),ρ(n+m+1)).
```

The same file constructs the persistent direction chain generated by each
initial event-wall direction. A varying tower field can therefore be pulled
back canonically to the fixed initial tangent frame. Summability of the
pulled-back one-step distances forces convergence to a field on that frame,
with the identical tail bound. Fields determined by event labels compatible
with every causal embedding are proved exactly constant after pullback.

This closes the first compactness and finite-variation convergence problem.
It controls every direction already present at level zero, but does not yet
control a field sector supported only on directions born later in the tower.
Such new-direction tightness, plus identification of a limiting topology and
differential structure, is required before calling the limit a continuum
connection or curvature tensor.

## Effective field equation

The minimal local quadratic action with height-shift symmetry is stated
explicitly:

```text
E_i = 1/2[(u_i-u_{i-1})²+(u_{i+1}-u_i)²] - J_i u_i.
```

`CAGBoundaryDynamics.localBoundaryEnergy_variation` proves exactly

```text
E_i(u_i+ε)-E_i(u_i)
  = ε(2u_i-u_{i-1}-u_{i+1}-J_i)+ε².
```

Thus a local minimum is equivalent to the discrete Poisson equation. With
spacing `a` and `J_i=a²ρ_i`, this is the centered discretization of
`-u''=ρ`. The variational implication is a theorem; selecting this action as
the continuum effective action is a modeling hypothesis still to be derived
from microscopic CAG weights.

`CAGFiniteCausalDynamics.lean` generalizes the exact variational calculation
to every finite graph and then specializes it to the downset graph of every
finite causal poset. With

```text
(Δ_G φ)(v) = Σ_{w~v}(φ(v)-φ(w)),
```

the star-local Dirichlet energy satisfies

```text
E_v(φ(v)+ε)-E_v(φ(v))
  = ε(Δ_G φ(v)-J(v)) + deg(v) ε²/2.
```

Therefore stationarity is exactly the graph Poisson equation `Δ_G φ=J`.
This discrete field equation is now available on arbitrary finite
causal-algebra state spaces. The choice of Dirichlet action remains an
explicit effective-model hypothesis rather than a consequence of the
microscopic causal-algebra weights.

## Conditional falsifiable prediction

The exact Fourier symbol of the field equation is

```text
λ(q)=2-2cos q=4sin²(q/2).
```

For wave speed `c` and lattice spacing `a`, the proposed linear dynamics gives

```text
ω²(q)=(c/a)²4sin²(q/2).
```

This agrees with a massless continuum mode at long wavelength and predicts a
specific ultraviolet deviation. It becomes physically falsifiable only if
`u`, `c`, and especially `a` are fixed by an independent CAG-to-observable
dictionary. Fitting `a` to the same dispersion data would not count as a
prediction.

## What has not been obtained

- no Lorentzian event-spacetime metric (the new arbitrary-`CAlg` metric is on
  downset states);
- no continuum Levi-Civita connection or Riemann/Ricci tensor (the proved
  connection is partial, discrete, and flat on its domain);
- no full nonradial or tensorial continuum theorem for arbitrary `CAlg`
  state spaces (the arbitrary-poset result is radial in event-count rank);
- no derivation of the Dirichlet action or physical length from microscopic
  CAG data;
- no Einstein field equation;
- no parameter-free numerical physical prediction.

The new files establish a mathematically coherent causal-state geometry and
its minimal effective dynamics. They deliberately do not overwrite the negative
result already recorded in `FinalStatus.lean`: regular-grid BD dynamics is not
Einstein gravity.

## Concrete uses supported by the proved structure

- exact comparison and nearest-state search using the valuation metric;
- canonical three-sample consensus and L¹ denoising via the unique median;
- exact shortest-path routing by admissible one-cell transitions;
- order-preserving interpolation through meet, join, and metric intervals;
- binary wall coordinates and Hamming-indexed search via the partial-cube
  embedding;
- the same exact algorithms on downset states of arbitrary finite causal
  algebras, no grid presentation required;
- local detection and counting of noncommuting causal moves through missing
  graph squares;
- reconstruction and counting of causal precedence across a state's active
  add/remove frontier from the exact mixed sectional-curvature kernel;
- metric-compatible comparison of persistent event directions across states,
  with covariant finite differences for directional data;
- presentation-independent comparison under causal-order isomorphism and
  isometric tracking of old versus new directions under past-closed growth;
- finite statistical-mechanics models whose configurations have an intrinsic
  rank, lattice operations, and boundary curvature;
- algorithmic coarse graining and multiscale coding of causal boundaries;
- a controlled state space on which effective actions can be proposed and
  audited without confusing a modeling hypothesis with a theorem.

The finite-poset generalization, cubical hyperplane/link construction,
arbitrary-dimensional independent-chain product scaling, intrinsic
`(2d+1)`-point operator, general coupled smooth-field consistency, and
causal-plaquette mixed Hessian are now proved. Arbitrary finite causal posets
also have an exact radial birth–death operator and a branching-controlled
smooth drift–diffusion limit. They now also have a complete finite nonradial
event frame, an exact frontier order-curvature kernel, a positive-definite
fiber metric with canonical flat partial transport, and functorial isometric
growth along past-closed refinements with an exact new-direction count.
Infinite compatible towers now have cumulative degree laws, linear-growth and
stabilization criteria, uniformly bounded normalized curvature, unconditional
curvature subsequential compactness, and full finite-variation convergence
with quantitative tail bounds. Persistent old-frame fields have the analogous
transported convergence theorem. The next mathematical frontier is tightness
and convergence for the directions born during refinement, followed by a
limiting topology and a continuum connection/curvature identification. A
physical field equation or parameter-free prediction additionally requires
derivation of the effective action and physical scale from microscopic CAG
data, followed by an observable dictionary.
