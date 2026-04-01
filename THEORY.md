# The Constrained Surface Theory — Final Status

## What Is Proved (Lean, zero sorry)

1. **Slab theorem:** Every convex subset of [m]^{d+1} is a slab between antitone boundaries
2. **Height bijection:** Downsets ↔ antitone functions
3. **Sharp threshold:** CC(k) = Free(k) for k ≤ m (one-line proof)
4. **Depth threshold:** T_d = (d+2)m − d for single violations
5. **One-contact theorem:** Violations at boundary only for k ≤ 3m−2
6. **Grand expansion structure:** Depth spacing m−1, core polynomials

## What Is Verified Numerically (strong evidence, not proved in Lean)

1. **Universal spectrum:** D(q)² = A000712 across all 2D contact sectors (8 sectors)
2. **Screening:** Θ_k = (k+1)m + d(m−k), spacing-independent (k=1−6, m≤24)
3. **Envelope slope:** d_max + gap_blocks + 2 (19 configurations)
4. **2D rational resummation:** Z = D²·(1−3z²+z³)/(1−z²+z³) (13 coefficients + convergence)
5. **Dimensional ladder:** Free tail = P_{d−1}² (d=2,3,4), contact = P²/(1−x)^{d−2} (d=2,3,4)
6. **3D contact core:** A091360 = partial sums of plane partitions (6 terms, m=6)

## What Is Measured (physical characterization)

1. **Correlations:** Exponential decay, ξ/m → f(β) ≈ 0.25−0.65
2. **No phase transition:** Z analytic on physical axis, β_c = expansion radius only
3. **Limit shape:** Controlled by comparability kernel eigenfunction on simplex
4. **Bulk gap:** 0.276 ± 0.001 from spectral computation (N=40−160)

## Continuum Operator Theory (d=2)

### The Exact Continuum Transfer Operator

Derived from the discrete slab transfer matrix (not guessed). The slab model
for [m]² has state (a,b) ∈ {0,...,m-1}² with a ≤ b, transfer T(s,s') = 1 iff
s' ≤ s componentwise. Rescaling u = a/(m-1), w = b/(m-1) to the triangle
Δ = {0 ≤ u ≤ w ≤ 1}, the Riemann limit gives:

**(𝒦f)(u,w) = ∫₀ᵘ ∫_{u'}^w f(u',w') dw' du'**

In simplex coordinates v = 1−w on Σ = {u,v ≥ 0, u+v ≤ 1}:

**(𝒦̃f̃)(u,v) = ∫₀ᵘ ∫_v^{1−u'} f̃(u',v') dv' du'**

The symmetrized operator K_s = (𝒦 + 𝒦†)/2 has kernel = ½ × comparability
indicator in the mixed product order (u'≤u, v'≥v or vice versa).

### Derived PDE

Differentiating the integral equation λ_s ψ = K_s ψ twice:

**ψ_{uv} = −(2/λ_comp) ψ = −μ ψ**

where λ_comp = eigenvalue of the comparability kernel, λ_s = λ_comp/2,
and μ = 1/λ_s = 2/λ_comp.

In wave coordinates s = u+v, d = v−u: **ψ_{ss} − ψ_{dd} = −μ ψ**
(Klein-Gordon equation on the simplex).

Numerically verified: ⟨ψ_{uv}/ψ⟩ = −5.24 vs expected −μ = −5.54 at N=50
(5% discretization error, improving with N).

### Eigenfunctions and Boundary Conditions

The unsymmetrized operator 𝒦 and its adjoint 𝒦† have distinct eigenfunctions
with clean local boundary conditions, derived from the integral equation:

- **Right eigenfunction ψ_R** (of 𝒦):
  - BC1: ψ_R(0, v) = 0 (Dirichlet at u=0), from (𝒦ψ)(0,v) = 0
  - BC2: ψ_{R,u}(u, 1−u) = 0 (Neumann on hypotenuse), from λψ_u = ∫_v^{1-u} ψ dv' at v=1−u

- **Left eigenfunction ψ_L** (of 𝒦†):
  - ψ_L(u,v) = ψ_R(v,u) by the u↔v symmetry exchanging 𝒦 and 𝒦†
  - BC1: ψ_L(u, 0) = 0 (Dirichlet at v=0)
  - BC2: ψ_{L,v}(u, 1−u) = 0 (Neumann on hypotenuse)

- **Symmetrized eigenfunction ψ_s** (of K_s = (𝒦+𝒦†)/2):
  - ψ_s(u,v) = ψ_R(u,v) + ψ_R(v,u), symmetric under u ↔ v
  - Nonzero at all boundaries (nonlocal integral boundary conditions)
  - The physically relevant bulk density is ψ_s²

Symmetry ψ_s(u,v) = ψ_s(v,u) verified to machine precision (2.8×10⁻¹⁶).

### Bessel-Mode Expansion

The general solution of ψ_{uv} = −μψ satisfying BC1 (ψ_R(0,v) = 0) is:

**ψ_R(u,v) = Σ_{p≥1} C_p (u/v)^{p/2} J_p(2√(μuv))**

where J_p are Bessel functions of the first kind. The eigenvalue condition
comes from BC2 (Neumann on hypotenuse u+v = 1):

**Σ_{p≥1} C_p (u/(1−u))^{(p-1)/2} J_{p-1}(2√(μu(1−u))) = 0  for all u ∈ (0,1)**

This couples ALL Bessel modes — separation of variables fails because BC2
mixes the radial (s = u+v) and angular (d = v−u) dependence.

The p=1 mode alone gives the 1D Bessel skeleton (ψ ~ J₁, gap ≈ 0.272).
The full solution with all modes gives the 2D gap γ₂ ≈ 0.276.
The angular correction Δγ ≈ 0.004 is genuinely non-perturbative:
it arises from the hypotenuse BC coupling all modes, not from
a small perturbation of the p=1 solution.

### Status

| Component | Status |
|-----------|--------|
| Operator derivation | Established (exact Riemann limit of discrete model) |
| PDE derivation | Numerically verified to discretization accuracy |
| Boundary conditions | Derived from integral equation, not guessed |
| Symmetry ψ_s(u,v) = ψ_s(v,u) | Exact (machine precision) |
| Bulk gap | Converging to γ₂ ≈ 0.2764 |
| Closed form for γ₂ | **Open** |
| d=3 continuum operator | **Open** (state space is infinite-dimensional) |

## What Is Open

1. **Exact closed form of the bulk gap γ₂.** The eigenvalue condition couples
   infinitely many Bessel modes. No closed-form solution is known.

2. **The d=3 continuum operator.** For d=3, the transfer matrix state is a pair
   of nonincreasing functions (not a point on a simplex), so the continuum limit
   is an operator on a function space. Transfer matrix computation gives
   γ₃(area/m²) = 0.549, 0.377, 0.291, 0.240 for m=2,3,4,5,6 (extrapolated
   γ₃ ≈ 0.04, but unreliable with few data points).

3. **Lean proofs of the screening theorem and block threshold.** Both need Finset
   sum-splitting (technical, not conceptual).

4. **Higher-dimensional contact resummation.** Can 3D/4D contact expansions be
   resummed into closed-form continuum partition functions like the 2D cubic ratio?

## The Complete Picture

The model is a **gapped constrained random surface** with:
- **Counting structure:** Dimension-stable, partition-theoretic, exactly solvable in 2D
- **Physical phase:** Confined, noncritical, ξ ∝ m, exponential correlations
- **Continuum operator:** (𝒦f)(u,v) = ∫₀ᵘ ∫_v^{1−u'} f(u',v') dv' du' on the simplex
- **PDE:** ψ_{uv} = −μψ (Klein-Gordon in wave coords), BCs derived from integral equation
- **Eigenfunction:** Bessel-Fourier expansion ψ_R = Σ C_p (u/v)^{p/2} J_p(2√(μuv))
- **Bulk gap:** γ₂ ≈ 0.2764, from the full Bessel-mode spectral problem (non-perturbative)

The theory connects to:
- Partition theory: A000712, A161870, A091360, A000293
- Integral operators: Comparability kernel on the simplex (exact continuum limit)
- Bessel functions: J_p modes in the eigenfunction expansion
- Klein-Gordon equation: PDE on the simplex with mixed BCs
- Statistical mechanics: Confined polymer expansion with rational resummation
