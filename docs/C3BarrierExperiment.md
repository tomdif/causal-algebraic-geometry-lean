# Exact c₃ barrier experiment

**Date:** August 16, 2026  
**Code:** `scripts/count_c3_barriers.py`

## Question

For boxed plane partitions `Ω_m`, does there exist an integer barrier `b_m`
for which both constrained families

```text
Below(b_m) = {φ ∈ Ω_m : φ ≤ b_m},
Above(b_m) = {ψ ∈ Ω_m : b_m < ψ}
```

lose only subquadratic entropy relative to `Ω_m`?  The Lean theorem
`C3BarrierLowerBound.barrier_product_le_Q` then gives

```text
|Below(b_m)| |Above(b_m)| ≤ Q(m).
```

For a self-dual barrier

```text
b(i,j) + b(m-1-i,m-1-j) = m-1,
```

complement-rotation is a bijection `Above(b) ≃ Below(b)`.  This is now
formalized by `aboveEquivBelowOfSelfDual`, and Lean proves the square bound

```text
|Below(b)|² ≤ Q(m).
```

## Exact method

A row state is a non-increasing `m`-tuple in `{0,...,m}`.  The sparse
transfer matrix has an edge `r → s` when `r ≥ s` componentwise.  Row masks
impose either `r ≤ b(i,-)` or `r > b(i,-)`.  The same transfer matrix gives
exact forward/backward messages and hence every one-point mean and median.

For `m ≤ 7`, all counts fit in signed 64-bit integers.  For `m=8`, the script
runs the transfer modulo

```text
1000000007, 1000000009, 998244353
```

and reconstructs with the Chinese remainder theorem.  Their product exceeds
`8 PP(8,8,8)`, so both counts and first moments are uniquely determined.
At every size the unrestricted transfer count is checked against MacMahon's
exact product; at `m=8` this check is made modulo all three primes.  Every
reconstructed one-point distribution is also checked to sum to MacMahon's
count.

Reproduce with:

```bash
python3 scripts/count_c3_barriers.py --max-m 8 --no-optimize
python3 scripts/count_c3_barriers.py --max-m 7 --sweeps 5
```

## Results

Let `PP_m = |Ω_m|`, `B_m = |Below(b_m)|`, and

```text
δ_m = (log PP_m - log B_m) / m.
```

Thus bounded `δ_m` means the stronger entropy estimate
`log PP_m - log B_m = O(m)`; the c₃ proof only needs this difference to be
`o(m²)`.

The `central-plane` barrier is the deterministic complementary rounding of

```text
clamp(3(m-1)/2 - i - j, 0, m-1).
```

For odd `m=2n+1`, no rounding choice is needed.  Its square lower bound is
formalized as `centralBarrierOdd_square_le_Q`.

| `m` | `PP_m` | central-plane `B_m` | central `δ_m` | best tested `B_m` | best `δ_m` | best `B_m²/Q(m)` |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 1 | 0.6931 | 1 | 0.6931 | 1.0000 |
| 2 | 20 | 3 | 0.9486 | 3 | 0.9486 | 0.4500 |
| 3 | 980 | 55 | 0.9601 | 55 | 0.9601 | 0.3441 |
| 4 | 232848 | 3390 | 1.0574 | 3487 | 1.0503 | 0.1357 |
| 5 | 267227532 | 1542041 | 1.0310 | 1542041 | 1.0310 | 0.1106 |
| 6 | 1478619421136 | 2196236253 | 1.0854 | 2254059744 | 1.0810 | 0.04175 |
| 7 | 39405996318420160 | 22861689652753 | 1.0646 | 22861689652753 | 1.0646 | not computed |
| 8 | 5055160684040254910720 | 773617447286148657 | 1.0981 | 773617447286148657 | 1.0981 | not computed |

The best tested barrier is coordinate-ascent optimized among self-dual
barriers through `m=7`.  At `m=8`, optimization was not run because each
objective evaluation requires three passes over a 34,763,300-edge matrix.

The exact finite-volume mean first differs materially from the central-plane
barrier at `m=8`.  After self-dual projection it gives

```text
B_8(mean) = 761947248081203566,
δ_8(mean) = 1.1000,
```

slightly worse than the explicit central-plane count.  Thus the near-linear
deficit pattern survives the first size at which the two candidate barriers
are genuinely distinct.

## What the experiment says

1. No tested natural self-dual barrier loses a visible positive entropy
   density.  Across `m=2,...,8`, the best one-sided deficit divided by `m`
   stays in the narrow range `0.9486` to `1.0981`.
2. The result is much stronger numerically than needed: it supports an
   `O(m)` deficit, while c₃ needs only `o(m²)`.
3. The raw lower-median barrier is invalid for this purpose.  It equals `m`
   at a frozen corner, so `Above(b)` is empty.  Complementary rounding or a
   boundary-layer patch is essential.
4. Search tuning adds little.  At `m=6` it improves `B_m` by only about 2.6%
   over the explicit central-plane barrier; at odd sizes through 7 it gives no
   improvement.

This is evidence, not an asymptotic proof.  Cohn--Larsen--Propp explicitly
show that the typical boxed-plane-partition surface is not the naive planar
half-filled-cube surface.  Small integer boxes can therefore conceal a later
quadratic loss.  The stable `m=8` result makes that failure less immediate,
but does not rule it out.

## The affine extrapolation is not the proof target

For odd `m=2n+1`, define

```text
b_n(i,j) = min(2n, max(0, 3n-i-j)),
B_n = |Below(b_n)|.
```

Equivalently, `B_n` is the number of order ideals of the rank-truncated
three-chain product

```text
P_n = {(i,j,k) ∈ [0,2n]² × [0,2n-1] : i+j+k < 3n}.
```

The finite data originally suggested the estimate

```text
log PP(2n+1,2n+1,2n+1) - log B_n = O(n).
```

That extrapolation is incompatible with the known nonplanar limit shape.
Because both the affine obstacle and the unique typical surface are
self-dual, feasibility of the typical surface below the obstacle would force
the two surfaces to agree.  They do not.  Thus the affine count must
eventually exhibit a positive `m²` entropy deficit; sizes through 8 are
pre-asymptotic.

## Replacement proof attack

The affine barrier is discarded.  The replacement is the shift-compression
argument in [`C3ShiftCompressionProof.md`](C3ShiftCompressionProof.md): take
the overwhelmingly large `o(m)`-radius tube around the actual limit surface,
shift it to both sides of a rounded barrier, and bound each shift fiber by a
thin-box MacMahon count.  This gives subquadratic loss without a one-sided
large-deviation theorem.
