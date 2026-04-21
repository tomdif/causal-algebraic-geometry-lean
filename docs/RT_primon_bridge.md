# Rodgers–Tao heat flow as primon-gas dynamics: a bridge check

**Date:** 2026-04-19. **Time-box:** 60 min. **Status:** formal correspondence constructed; rigor requires controlling a contour-shift and a Gaussian-convolution identity on the critical line.

## 1. Literature check

I found **no paper that writes out the RT flow as a dynamics in the primon-gas β variable**.
What exists:

- Rodgers–Tao, *The de Bruijn–Newman constant is non-negative* (arXiv:1801.05914). Uses backward heat-equation language in the Fourier variable `u`, not in primon β.
- Tao–Polymath15, *Effective approximation...* (arXiv:1904.12438). Same framing.
- Newman–Wu (Bull AMS 2020), *Constants of de Bruijn–Newman type in analytic number theory and statistical physics*. Closest spiritually — discusses Lee–Yang-like interpretations, but does **not** identify Λ with a primon-gas observable.
- Bost–Connes (1995) and Connes–Marcolli (2008): primon / BC system, KMS states, spontaneous symmetry breaking at β=1. They do **not** touch Rodgers–Tao.
- "Conformal primon gas at the end of time" (arXiv:2502.02661): generalised primon gases, no RT.

Conclusion: **not in the literature**, at least not written out. The construction below is new as an explicit symbolic bridge.

## 2. Explicit symbolic bridge

**Rodgers–Tao flow.** With Φ as in Rodgers–Tao,
  H_t(z) = ∫_{-∞}^{∞} e^{t u²} Φ(u) cos(zu/2) du / 8,
the map `t ↦ H_t` is, at the Fourier-kernel level, multiplication by `e^{t u²}` on the `u`-axis.

**Theta side.** Substituting τ = e^{2u} converts Φ to a combination of derivatives of the Jacobi theta function ω(τ) = Σ e^{−π n² τ}. On the multiplicative line R₊ with Haar measure dτ/τ, the Mellin transform M is the Fourier transform of the multiplicative group. Under the change u = ½ log τ, multiplication by `e^{t u²}` becomes multiplication by `exp((t/4)(log τ)²)` — a **log-normal multiplier** on R₊.

**Mellin pushforward.** The Mellin transform of a log-normal multiplier acts by Gaussian convolution on the Mellin-dual variable s. Explicitly, for a Schwartz function f on R₊ with Mellin transform F(s),

  M[ exp((t/4)(log τ)²) f(τ) ](s)
    = (1/√(4π t)) ∫_{Re s' = Re s} exp(−(s − s')²/(4t)) F(s') ds'    ... (∗)

which is a vertical-line convolution. As a pseudo-differential operator, (∗) is

  **e^{ t · ∂_s² }** ,

i.e. a **forward** heat flow in the Mellin/primon-β variable (note the sign flip relative to z, consistent with Fourier/Mellin duality: `∂_u ↔ ∂_s`, so `e^{t u²}` in u becomes `e^{t ∂_s²}` in s).

**Bridge.** Identifying s with primon inverse-temperature β and Z(β) = ζ(β),

  **(RT_t Z)(β) := e^{ t · ∂_β² } Z(β)**

formally equals the Mellin transform of the RT-deformed theta kernel, and its zeros on the critical line `Re β = ½` are the zeros of H_t(z) under z = −2i(β − ½).

### Primon-gas meaning of ∂_β²

For the primon gas, `Z(β) = Σ n^{−β} = Σ e^{−β E_n}` with E_n = log n. Direct:

  ∂_β Z = −⟨E⟩ Z,
  ∂_β² Z = ⟨E²⟩ Z,

where ⟨·⟩ is the unnormalised Boltzmann sum. Hence the RT flow is

  ∂_t Z_t = ⟨E²⟩_β · Z_t   (at leading order),

and the full flow is the **Gaussian average of Z over imaginary shifts of β**:

  Z_t(β) = E[ Z(β + i √(2t) · X) ],   X ~ N(0,1),

i.e. RT smoothes Z against imaginary-β fluctuations of variance 2t. Equivalently, it is the heat semigroup on the imaginary-chemical-potential direction.

### Interpretation of Λ

Under this dictionary:

- **Λ > 0** ⇔ Z(β) on the critical line has complex zeros (off `Re β = ½`). Gaussian smoothing of strength ≥ Λ is needed to push all zeros onto the line. Thermodynamically: the primon partition function, viewed as an analytic function of complex β, has a zero pattern off the symmetry line that imaginary-β fluctuations of variance ≥ 2Λ wash out.
- **Λ = 0 (RH)** ⇔ zeros already lie on the critical line. No imaginary-β smoothing is needed: the symmetry point `Re β = ½` already pins all zeros.
- **Λ < 0** ⇔ already-real zeros remain real under **reverse** heat. Since reverse heat concentrates mass, this would be a strong rigidity statement; Rodgers–Tao ruled it out (Λ ≥ 0).

So in primon language: **Λ is the minimal imaginary-chemical-potential fluctuation variance needed to enforce reflection symmetry β ↔ 1−β at the level of zeros.** RH says the free-primon-gas zero set is already reflection-symmetric with no smoothing. Rodgers–Tao says you never need reverse smoothing.

## 3. Is this rigorous?

**No — formal, not rigorous.** Three points where it must be checked:

1. **Domain of `e^{t ∂_β²}`.** Z(β) = ζ(β) is not Schwartz on vertical lines; it grows polynomially and has a pole at β=1. The operator `e^{t ∂_β²}` as vertical convolution requires decay controls. Rodgers–Tao work with ξ(s) (gamma-completed; rapid decay on vertical lines), not ζ(s). The clean statement is in ξ, not Z. So the RT-flow-on-primon-Z formulation is **only formal unless you work with the completed ξ**, where ξ-zeros = primon-Z-critical-line-zeros but the function is not literally the primon partition function — it is Z times a gamma factor (≈ closed-string tachyon factor).

2. **Contour / convolution (∗)**. The identity (∗) requires that the convolution integral converges on the relevant vertical line and commutes with the inverse Mellin that reconstructs H_t. Standard for Schwartz inputs; Φ gives Schwartz decay, so this step is in fact fine for ξ.

3. **Sign of ∂_β²**. Forward heat in β gives ξ-side smoothing; the "backward heat" framing in the Tao post refers to the z-variable. These are consistent once the Fourier/Mellin duality is tracked; the sign flip is not a problem but is easy to get wrong.

## 4. What it would take to promote to rigorous

Short version: *rewrite the entire Rodgers–Tao setup replacing u by log-primon-temperature and absorbing the gamma factor into the definition of a completed primon partition function Ẑ(β) = π^{−β/2}Γ(β/2)Z(β).* Then (RT_t Ẑ)(β) = e^{t ∂_β²} Ẑ(β) rigorously on `Re β = ½` by the standard Weierstrass-transform theorem for functions of Gaussian-bounded vertical decay (Ẑ satisfies this on strips). Λ becomes the infimum of `t` such that `e^{t ∂_β²} Ẑ` has zeros only on `Re β = ½`. This is a theorem, not a conjecture, **conditional on choosing Ẑ and not Z.**

The honest assessment: **the bridge is real, but it is a bridge to completed-ξ primon gas, not to the bare Julia primon gas.** The completed ξ is a primon gas coupled to a "gamma-factor reservoir" (an infinite tower of oscillators — the archimedean place, in adelic language). Without the gamma factor, ζ(β) does not decay vertically fast enough for the Weierstrass transform to be globally defined, and Λ does not have a clean primon-observable meaning.

## 5. Real bridge or renaming?

**Partially real, partially renaming.**

- **Real content:** the identification of `e^{t ∂_β²}` as a fluctuation of imaginary chemical potential is physically meaningful. It says Rodgers–Tao is the semigroup generated by `-⟨E²⟩` (energy-squared variance) acting on the analytic continuation of the partition function to complex β. This is a primon-gas observable: the variance of the energy in the ensemble Z. The role of Λ as the critical imaginary-fluctuation-strength is a genuine thermodynamic statement.
- **Renaming:** only once you accept that "primon gas" means the completed primon gas (with gamma-factor oscillators). The bare Julia gas does not see the functional equation β ↔ 1−β, which is supplied entirely by the gamma factor. RH is a statement about the *symmetric* ξ, and the bare Julia gas has no such symmetry — so any "bridge" that claims bare-Z status is renaming.
- **Net:** the correspondence is a genuine reformulation (not a tautology) provided one uses completed-Ẑ. It does not immediately give a proof strategy but it does furnish a physical picture for Λ as a fluctuation-variance threshold, which is not obvious in the Fourier-u language.

## 6. Key formulas (for reuse)

```
RT flow on H_t:        H_t(z) = F_u^{-1}[ e^{t u²} · F_u[H_0] ](z)         Fourier in u
                                = e^{-t ∂_z²} H_0(z)                       backward heat in z

Mellin bridge:         τ = e^{2u},    s = β = ½ + iz/2,
                       ξ(β) = const · M[ theta-derivative kernel ](β),
                       completed Ẑ(β) = π^{-β/2} Γ(β/2) ζ(β) = ξ(β)/(½ β(β−1))

Primon-side flow:      Ẑ_t(β) = e^{t ∂_β²} Ẑ(β)                             forward heat in β
                             = E[ Ẑ(β + i√(2t) X) ],  X ~ N(0,1)

Energy observable:     ∂_β² Z = Σ (log n)² n^{-β} = ⟨E²⟩·Z  (bare primon gas)

Λ interpretation:      Λ = inf{ t ≥ 0 : zeros of Ẑ_t all on Re β = ½ }
                       = minimal imag-β Gaussian variance / 2 enforcing
                         reflection-symmetric zero set.
```

## 7. Open questions suggested by the bridge

1. **Lee–Yang for imaginary β**: is there a Lee–Yang-type theorem saying the zeros of Ẑ in complex β all lie on a single line for all primon gases (with suitable weights)? If yes, Λ=0 follows automatically. Newman–Wu gesture at this but do not conclude.
2. **Commutator of RT with Euler product.** The Euler product `ζ(β) = ∏(1−p^{-β})^{-1}` is destroyed by `e^{t ∂_β²}` (products don't commute with convolution). The flow is natural on the additive (log-n) side, not the multiplicative (prime) side. **This is the real obstruction** to using RT to attack RH through the primes: RT smoothing breaks the Euler product.
3. **Dual flow on primes.** Is there a dual heat flow acting on the *prime* index that is conjugate to RT via log? If so, it would be an evolution on the prime counting function — a completely different object.

## Sources

- [1801.05914 — Rodgers, Tao. The de Bruijn-Newman constant is non-negative](https://arxiv.org/abs/1801.05914)
- [1904.12438 — Polymath15. Effective approximation of heat flow evolution of ξ](https://arxiv.org/abs/1904.12438)
- [Newman, Wu. Constants of de Bruijn-Newman type in analytic number theory and statistical physics. Bull AMS 2020](https://www.ams.org/journals/bull/2020-57-04/S0273-0979-2019-01668-1/)
- [Primon gas — Wikipedia](https://en.wikipedia.org/wiki/Primon_gas)
- [Tao blog, 2018 post on Λ ≥ 0](https://terrytao.wordpress.com/2018/01/19/the-de-bruijn-newman-constant-is-non-negativ/)
- [2502.02661 — Conformal primon gas at the end of time](https://arxiv.org/abs/2502.02661)
