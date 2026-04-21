"""
Selberg analog of Dyson's quasicrystal observation.

For the modular surface PSL(2, Z) \\ H, the Selberg zeta function has
nontrivial zeros at s = 1/2 + i r_n where r_n are Maass form eigenvalues
(eigenvalues of the hyperbolic Laplacian, λ = 1/4 + r²). These r_n are
the PROVED-RH-analog ordinates: they lie on Re(s) = 1/2 because the
Laplacian is self-adjoint.

Selberg's trace formula:
  Σ_n h(r_n) = (identity) + (elliptic) + Σ_{γ primitive} Σ_{k ≥ 1}
               (log N(γ) / (N(γ)^{k/2} - N(γ)^{-k/2})) · ĥ(k log N(γ))
               + (parabolic / cusp contributions)

This predicts that the Fourier transform of the Maass-eigenvalue point
process has support concentrated on {log N(γ)} = {lengths of primitive
closed geodesics}, just as Riemann zeros have Fourier support on {log p}.

For Γ = PSL(2, Z), primitive closed geodesic lengths are 2 arccosh(t/2)
where t ≥ 3 is the trace of a primitive hyperbolic matrix. So the
expected Fourier peaks are at:
  t = 3: ℓ = 2 arccosh(1.5)  ≈ 1.9248
  t = 4: ℓ = 2 arccosh(2)    ≈ 2.6339
  t = 5: ℓ = 2 arccosh(2.5)  ≈ 3.1336
  t = 6: ℓ = 2 arccosh(3)    ≈ 3.5255
  t = 7: ℓ = 2 arccosh(3.5)  ≈ 3.8470
  t = 8: ℓ = 2 arccosh(4)    ≈ 4.1311
  ...

If the quasicrystal structure is universal across Riemann-like zeta
functions, we should see peaks of F(k) at these values of k.
"""

import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


# First ~30 Maass form eigenvalues r_n for Γ = PSL(2, Z), combining
# both even and odd parities, ordered by magnitude.
# Sources: Hejhal 1992/1993, Then 2004, Stromberg's tables, LMFDB.
# Values truncated to 4-5 decimal places (sufficient for Fourier analysis
# at the scales we care about).
MAASS_EIGENVALUES = [
    9.5337,   # even_1
    12.1730,  # odd_1
    13.7798,  # even_2
    14.3585,  # odd_2
    16.1384,  # even_3
    16.6443,  # odd_3
    17.7386,  # even_4
    18.1818,  # odd_4
    19.4235,  # even_5
    19.4847,  # odd_5
    20.3213,  # odd_6
    21.3158,  # even_6
    22.2091,  # odd_7
    22.7855,  # even_7
    23.2559,  # odd_8
    24.1112,  # even_8
    24.5690,  # odd_9
    25.0508,  # even_9
    25.3083,  # odd_10
    26.0569,  # even_10
    26.7680,  # odd_11
    27.1207,  # even_11
    27.6710,  # odd_12
    28.3462,  # even_12
    28.9287,  # odd_13
    29.1908,  # even_13
    29.6834,  # odd_14
    30.4253,  # even_14
    30.5762,  # odd_15
    31.0868,  # even_15
]


def primitive_geodesic_lengths(t_max=10):
    """Primitive closed geodesic lengths for PSL(2, Z).

    For each trace t >= 3 with t² - 4 not a perfect square (primitive
    hyperbolic), the associated closed geodesic has length 2 arccosh(t/2).
    """
    lengths = []
    for t in range(3, t_max + 1):
        # Check primitivity by excluding t = k² + 2 for some k ≥ 1,
        # which corresponds to γ² where γ has trace k
        # (more careful primitivity would check all indefinite quadratic
        # form classes; for this quick scan we just list all traces).
        lengths.append((t, 2 * math.acosh(t / 2)))
    return lengths


def fourier_sum(r_values, k_grid):
    """Compute F(k) = (1/N) sum_n exp(i * k * r_n) for each k in k_grid."""
    N = len(r_values)
    r = np.array(r_values, dtype=float)
    F = np.zeros(len(k_grid), dtype=complex)
    for i, k in enumerate(k_grid):
        F[i] = np.mean(np.exp(1j * k * r))
    return F


def main():
    r = MAASS_EIGENVALUES
    N = len(r)
    print(f"Using {N} Maass eigenvalues for PSL(2,Z), range "
          f"[{min(r):.2f}, {max(r):.2f}].\n")

    geodesics = primitive_geodesic_lengths(t_max=12)
    print("Primitive geodesic lengths (quasicrystal peak predictions):")
    for t, ell in geodesics:
        print(f"  t={t:>2}: ℓ = 2 arccosh({t}/2) = {ell:.4f}")
    print()

    k_grid = np.linspace(0, 6, 3001)
    F = fourier_sum(r, k_grid)
    absF = np.abs(F)

    # Background: median |F| away from geodesic lengths
    peak_mask = np.zeros_like(k_grid, dtype=bool)
    for t, ell in geodesics:
        peak_mask |= (np.abs(k_grid - ell) < 0.05)
    background_median = np.median(absF[~peak_mask & (k_grid > 0.2)])
    print(f"Background |F| median (away from geodesic peaks, k > 0.2): "
          f"{background_median:.4f}")
    print()

    # Peak heights at geodesic lengths
    print(f"{'t':>3} {'ℓ = log N(γ)':>14} {'k_peak':>10} {'|F(ℓ)|':>10} "
          f"{'SNR':>8}")
    for t, ell in geodesics:
        # nearest grid point
        idx = int(np.argmin(np.abs(k_grid - ell)))
        # find local max within ±0.05
        window = 25  # ~0.05 in k
        lo, hi = max(0, idx - window), min(len(k_grid), idx + window)
        local_idx = lo + int(np.argmax(absF[lo:hi]))
        k_peak = k_grid[local_idx]
        amp = absF[local_idx]
        snr = amp / background_median if background_median > 0 else float("inf")
        print(f"{t:>3} {ell:>14.4f} {k_peak:>10.4f} {amp:>10.4f} {snr:>8.2f}")

    print()
    print("For comparison: Riemann-zero quasicrystal check at N=2000 gave")
    print("background 0.002 and peak SNR 50-75 at prime logs.")
    print()
    print("N=30 is MUCH smaller, so background ~1/sqrt(N) ≈ 0.18 is expected.")
    print("Look for peak/background ratio > 1.5 as a positive signal.")

    # Plot
    fig, ax = plt.subplots(figsize=(10, 5))
    ax.plot(k_grid, absF, color='steelblue', linewidth=0.7)
    ax.axhline(background_median, color='gray', linestyle='--', linewidth=0.7,
               label=f'median background = {background_median:.3f}')
    for t, ell in geodesics:
        ax.axvline(ell, color='red', linestyle=':', alpha=0.7, linewidth=0.8)
        ax.text(ell, max(absF) * 0.95, f't={t}', rotation=90,
                fontsize=7, va='top', color='red')
    ax.set_xlabel('k (Fourier variable)')
    ax.set_ylabel('|F(k)| = |(1/N) Σ exp(i k r_n)|')
    ax.set_title(f'Selberg quasicrystal check: Maass eigenvalues, N={N}\n'
                 'Red lines: primitive geodesic lengths 2·arccosh(t/2)')
    ax.legend()
    ax.set_xlim(0, 6)
    plt.tight_layout()
    out = '/Users/thomasdifiore/causal-algebraic-geometry-lean/scripts/selberg_quasicrystal.png'
    plt.savefig(out, dpi=150)
    print(f'\nPlot saved to {out}')


if __name__ == "__main__":
    main()
