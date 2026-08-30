# The c₃ shift-compression argument

**Status (August 2026):** the finite tube theorem remains valid, but the
limit-shape input described below has been superseded by the deterministic
quantization theorem in `C3MultiscaleCompression.lean`. The new argument is
strictly stronger for the entropy problem: it needs neither uniform
limit-shape concentration nor rectangular MacMahon. See
[`C3ResearchFrontier.md`](C3ResearchFrontier.md) for the current proof.

The rest of this document records the original limit-shape specialization of
the tube theorem. It is still relevant to fluctuation questions, but no longer
to the proof of the leading constant.

## 1. The large tube

Write `Ω_m` for the antitone height profiles `[m]² → {0,...,m}` and `N_m` for
`|Ω_m| = PP(m,m,m)`.

Cohn--Larsen--Propp's Theorem 1.2 gives a deterministic limit height and says
that, for every fixed `ε>0`, the probability of a uniform random tiling
differing from it anywhere by more than `εm` is exponentially small in
`m²`.  The plane-partition/lozenge correspondence is an affine change of
height coordinates, so this supplies integer barriers `b_m` and a diagonal
sequence `k_m=o(m)` for which

```text
T_m = {h ∈ Ω_m : |h(x)-b_m(x)| ≤ k_m for every x}
```

satisfies

```text
|T_m|/N_m → 1.
```

Round and clip the barrier so that `0 ≤ b_m(x) < m`.  This changes its
distance from the limiting profile by at most a constant, which is absorbed
by `k_m`.

The diagonal sequence requires no uniform rate in `ε`: choose a threshold
for `ε=1`, then for `ε=1/2`, and so on, and let `ε_m` decrease only after the
corresponding threshold has been crossed.

## 2. Shift the tube to opposite sides

For `h∈Ω_m`, define

```text
D_k(h)(x) = max(h(x)-k, 0),
U_k(h)(x) = min(h(x)+k, m).
```

Both maps preserve antitonicity.  For `h∈T_m`,

```text
D_k(h) ≤ b_m,
b_m < U_(k+1)(h).
```

Consequently,

```text
D_k(T_m) ⊆ Below(b_m),
U_(k+1)(T_m) ⊆ Above(b_m).
```

The extra unit in the upward shift is exactly what converts the lower tube
inequality into a strict inequality, including on frozen facets.

## 3. The fibers are thin plane partitions

The down-shift loses only

```text
R_k(h)(x) = min(h(x),k).
```

This residual is a plane partition in an `m×m×k` box, and

```text
h = D_k(h) + R_k(h).
```

Thus `h ↦ (D_k(h),R_k(h))` is injective.  Every down-shift fiber has size at
most `PP(m,m,k)`.  Complement-rotation gives the identical statement for the
up-shift.  Therefore

```text
|Below(b_m)| ≥ |T_m| / PP(m,m,k_m),
|Above(b_m)| ≥ |T_m| / PP(m,m,k_m+1).
```

Lean avoids division and proves the stronger exact integral packaging

```text
|T_m|² ≤ Q(m) PP(m,m,k_m) PP(m,m,k_m+1).
```

This is theorem `C3ShiftCompression.tube_square_le_Q_mul_thin`.

## 4. Thin boxes cost only subquadratic entropy

Telescoping MacMahon's product in the thin direction gives

```text
log PP(m,m,k)
  = Σ_{1≤i,j≤m} log(1 + k/(i+j-1)).
```

Group the summands by `s=i+j-1`.  There are at most `s` pairs with a given
`s`, and `log(1+k/s)≤k/s`, hence

```text
log PP(m,m,k) ≤ (2m-1)k < 2mk.
```

For `k_m=o(m)`, both thin factors are therefore `exp(o(m²))`.

## 5. Entropy conclusion

The finite theorem gives

```text
log Q(m)
  ≥ 2log|T_m|
    - log PP(m,m,k_m)
    - log PP(m,m,k_m+1)
  = 2log N_m - o(m²).
```

The reverse inequality `Q(m)≤N_m²` is immediate because a full-support pair
is a pair of plane partitions.  MacMahon's cubic-box asymptotic then yields

```text
log Q(m)/m² → 2L₃.
```

Combined with the existing convex-set sandwich, this is the desired
`c₃=2L₃` conclusion.

## 6. Why the affine barrier is discarded

The central-plane barrier from the finite experiment is self-dual.  The
unconstrained entropy maximizer is also self-dual and unique.  If it lay
weakly below the affine barrier everywhere, complement-rotation would force
it to lie weakly above it everywhere, hence to equal the affine plane.
Cohn--Larsen--Propp explicitly prove that the typical surface is not this
plane.  The affine obstacle therefore excludes the unique maximizer and must
lose a positive entropy density asymptotically, despite its convincing
`m≤8` behavior.

The shift-compression proof uses the actual limit surface and does not need
the all-positive ordering event to be typical.  Nor does it require a
profile-local variational lower bound: the large unconstrained tube is
compressed into the two constrained families with controlled fibers.

## Primary input

- [Cohn, Larsen, Propp, *The Shape of a Typical Boxed Plane Partition*](https://emis.de/ft/22395), especially Theorem 1.2: uniform limit height and exponentially small probability of a macroscopic sup-norm deviation.
