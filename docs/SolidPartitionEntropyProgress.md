# Solid-partition entropy: proved extension and remaining problem

This investigation extends the cubic compression argument to boxed solid
partitions and constructs exact-volume interfaces. It does not solve the
solid-partition asymptotic problem or establish that the new comparison
theorem is original in the literature.

## The unconditional theorem

Let `D_j(m)` count downsets of the coordinate-ordered grid `[m]^j`, and let
`C_j(m)` count its order-convex subsets. Let `Q_d(m)` count pairs of antitone
height profiles on `[m]^d` that are strictly separated at every base point.
In dimension four, `D_4(m)` is the number of solid partitions with all four
diagram coordinates bounded by `m`.

For every `r >= 0` and `m >= 1`, define

```
k = floor(sqrt(m)) + 1
E_r(m) = m^r * (1 + 2*m*floor(m/(k+1)) + m*k + m*(k+1)).
```

The new module proves

```
D_(r+3)(m)^2 <= Q_(r+2)(m) * 16^E_r(m),
Q_(r+2)(m) <= C_(r+3)(m) <= D_(r+3)(m)^2,
E_r(m) <= m^r * (1 + 4*m*floor(sqrt(m)) + 3*m).
```

Consequently,

```
0 <= 2*log D_(r+3)(m) - log C_(r+3)(m) <= E_r(m)*log 16,
(2*log D_(r+3)(m) - log C_(r+3)(m)) / m^(r+2) -> 0.
```

For solid partitions the absolute logarithmic error is `O(m^(5/2))`,
which is lower order than the boundary scale `m^3`. No one-boundary limit,
MacMahon formula in dimension four, or limit-shape hypothesis is assumed.

The proof uses the existing general-dimensional shift/residual injections
and height quantization. Threshold-layer encoding bounds a thin profile by
a tuple of lower-dimensional downsets. The existing dimension law controls
the cost of those tuples. Thus the dependence on the two-dimensional base
in the original entropy proof was removable.

Implementation: `CAGMultidimensionalEntropy.lean`.

## Exact-volume results

Write `a_(d,m)(n)` for the number of antitone profiles on `[m]^d`, with heights
at most `m`, whose heights sum to exactly `n`. The second new module proves:

1. `D_(d+1)(m) = sum_(n=0)^(m^(d+1)) a_(d,m)(n)`.
2. If `n < m`, then `a_(d,m)(n) = p_d(n)`, using the existing finite-support
   stabilization equivalence. `solidPartitionCount` is the genuine finite
   cardinality `p_3(n)`, not the older finite lookup table.
3. Some `n <= m^(d+1)` satisfies
   `D_(d+1)(m) <= (m^(d+1)+1) * a_(d,m)(n)`.
4. Volume is 1-Lipschitz for the boundary cell metric. Two profiles with
   the same quantization code at block size `k+1` differ in volume by at
   most `m^d*k`.

The third result gives an entropy-maximizing coefficient up to logarithmic
loss. It does not locate that coefficient or prove unimodality. The fourth
result controls approximate scaled volume, not exact volume preservation.

Implementation: `CAGSolidPartitionVolume.lean`.

## Exact finite experiment

Run:

```sh
python3 scripts/solid_partition_entropy_probe.py
```

The program enumerates downsets of `[m]^3`, then counts decreasing chains of
`m` such downsets with integer polynomial weights recording volume. It checks
the transfer-state count against MacMahon's plane-partition formula, checks
box-complement symmetry, and compares with direct four-dimensional downset
enumeration for `m <= 2`. It requires no third-party Python packages.

| Box side | Boxed solid partitions | Largest volume coefficient | Maximizing volumes |
|---|---:|---:|---|
| 1 | 2 | 1 | 0, 1 |
| 2 | 168 | 24 | 8 |
| 3 | 17,792,748 | 828,966 | 40, 41 |

These are independent Python computations, not kernel-verified numerical
certificates. The small-box central maxima do not establish a general
central-maximum theorem or an asymptotic constant.

## What would still constitute the breakthrough

The target remains a theorem

```
log p_3(n) = c*n^(3/4) + o(n^(3/4)),
```

with a proved characterization of `c` and ideally convergent computable upper
and lower bounds. The present factorization compares two unknown entropies;
it does not evaluate either one.

The next substantial inputs are a volume-dependent entropy estimate for
large boxes and control of shapes extending beyond boxes at the natural
linear scale `n^(1/4)`. Stabilization at `m > n` is exact but much too coarse
to provide that control. The large-coefficient result also leaves its volume
unspecified, so it cannot by itself produce an asymptotic for every `n`.

A useful next test is to establish matching finite bounds for prescribed
volume-density intervals while explicitly tracking the quantization volume
error. This must precede any claim of an effective determination of `c`.

For context, the primary research literature includes
[Yeliussizov's partition bounds](https://arxiv.org/abs/2302.04799) and
[Destainville--Govindarajan's numerical asymptotics](https://arxiv.org/abs/1406.5605).
Numerical estimates in the latter are not used in any Lean proof.

## Verification

The full default `lake build` passes (3,485 jobs). Three new `FinalCheck`
endpoints have guarded axiom reports containing only `propext`,
`Classical.choice`, and `Quot.sound`. No new mathematical axioms or
unfinished proof placeholders were added.
