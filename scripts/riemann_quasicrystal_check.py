"""
Test Dyson's 2009 conjecture that the Riemann zeros form a 1D quasicrystal:
the Fourier sum F(k) = (1/N) sum_n exp(i k t_n) over zero ordinates t_n
should have pure-point support at k = +/- log p for primes p.

This is a direct numerical probe of the Riemann explicit formula.
"""

import os
import time
import numpy as np
import mpmath
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS_CACHE = os.path.join(HERE, "riemann_zeros_cache.txt")

# -----------------------------------------------------------------------------
# 1. Obtain the first N Riemann-zeta nontrivial-zero ordinates t_n.
# -----------------------------------------------------------------------------
def load_or_compute_zeros(N: int) -> np.ndarray:
    """Load t_n from cache; if fewer than N, compute the rest via mpmath."""
    cached = []
    if os.path.exists(ZEROS_CACHE):
        with open(ZEROS_CACHE) as f:
            for line in f:
                line = line.strip()
                if line:
                    cached.append(float(line))
    if len(cached) >= N:
        return np.array(cached[:N])
    # Compute remaining
    print(f"Have {len(cached)} cached zeros; computing up to {N} via mpmath...")
    mpmath.mp.dps = 25  # 25 digit precision is ample for t_n up to n=10^4
    start = time.time()
    with open(ZEROS_CACHE, "a") as f:
        for n in range(len(cached) + 1, N + 1):
            t = float(mpmath.im(mpmath.zetazero(n)))
            cached.append(t)
            f.write(f"{t:.15f}\n")
            if n % 100 == 0:
                print(f"  n={n}  t_n={t:.6f}  elapsed={time.time()-start:.1f}s")
    return np.array(cached[:N])


# -----------------------------------------------------------------------------
# 2. Compute F(k).  For real k and real ordinates t_n, F(k) is Hermitian:
#       F(-k) = conj(F(k))
#    so |F(k)| is an even function and we only scan k >= 0.
# -----------------------------------------------------------------------------
def fourier_sum(t: np.ndarray, k_grid: np.ndarray) -> np.ndarray:
    # Outer product (len(k), len(t))
    phases = np.exp(1j * np.outer(k_grid, t))
    F = phases.sum(axis=1) / len(t)
    return F


# -----------------------------------------------------------------------------
# 3. Prime log table and a robust local-max extraction around each expected peak.
# -----------------------------------------------------------------------------
PRIMES_SMALL = [2, 3, 5, 7, 11, 13, 17, 19]


def sieve(limit: int):
    s = np.ones(limit + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(limit**0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return [int(p) for p in np.where(s)[0]]


def peak_near(k_grid: np.ndarray, absF: np.ndarray, k0: float, window: float = 0.03):
    """Return (k_peak, height) — the maximum of |F| inside [k0-window, k0+window]."""
    mask = (k_grid >= k0 - window) & (k_grid <= k0 + window)
    if not mask.any():
        return k0, float("nan")
    idx_local = np.argmax(absF[mask])
    idx_global = np.where(mask)[0][idx_local]
    return float(k_grid[idx_global]), float(absF[idx_global])


# -----------------------------------------------------------------------------
# 4. Run.
# -----------------------------------------------------------------------------
def main():
    N = 2000  # Time-boxed; ~60s of compute for a fresh run, near-instant if cached.
    t = load_or_compute_zeros(N)
    print(f"Loaded N = {len(t)} zero ordinates. t_1={t[0]:.6f}, t_N={t[-1]:.6f}")

    # Grid: 0 .. 10 at step 0.001  → 10001 points.  Needed to resolve peaks
    # whose "width" under N=2000 is O(2π / (t_N - t_1)) ≈ 0.002.
    k_grid = np.arange(0.0, 10.0 + 1e-12, 0.001)
    print(f"Grid: {len(k_grid)} k-points in [0, 10].")

    t0 = time.time()
    F = fourier_sum(t, k_grid)
    absF = np.abs(F)
    print(f"F(k) computed in {time.time()-t0:.1f}s. max|F|={absF.max():.4f}")

    # Expected-peak table: p, log p, measured k-peak, measured |F|
    rows = []
    for p in PRIMES_SMALL:
        k_expected = np.log(p)
        k_peak, h = peak_near(k_grid, absF, k_expected, window=0.03)
        rows.append((p, k_expected, k_peak, h))

    # Prime squares p^2 for p = 2,3,5 (log p^2 = 2 log p)
    squares = []
    for p in [2, 3, 5, 7]:
        k_expected = 2.0 * np.log(p)
        if k_expected <= k_grid[-1]:
            k_peak, h = peak_near(k_grid, absF, k_expected, window=0.03)
            squares.append((p * p, k_expected, k_peak, h))

    # Background level: median of |F| on grid away from any prime-power log.
    primepower_ks = set()
    for p in sieve(200):
        pk = 1
        for m in range(1, 8):
            pk *= p
            if pk > 1:
                kk = np.log(pk)
                if kk < 10:
                    primepower_ks.add(round(kk, 3))
    bg_mask = np.ones_like(k_grid, dtype=bool)
    for kk in primepower_ks:
        bg_mask &= np.abs(k_grid - kk) > 0.05
    # Also exclude tiny k where F→1 trivially
    bg_mask &= k_grid > 0.2
    bg_median = float(np.median(absF[bg_mask]))
    bg_p95 = float(np.percentile(absF[bg_mask], 95))
    bg_max = float(np.max(absF[bg_mask]))

    # ---- Report ----
    print("\n" + "=" * 68)
    print(f"Dyson quasicrystal test at N = {N}")
    print("=" * 68)
    print(f"\nBackground |F| away from prime-power logs (k>0.2):")
    print(f"  median = {bg_median:.4f}    95th pct = {bg_p95:.4f}    max = {bg_max:.4f}")
    print(f"\nPeaks at k = log p  (primes):")
    print(f"  {'p':>4} {'log p':>10} {'k_peak':>10} {'|F|':>10} {'SNR':>8}")
    for p, ke, kp, h in rows:
        snr = h / bg_median if bg_median > 0 else float("inf")
        print(f"  {p:>4} {ke:>10.5f} {kp:>10.5f} {h:>10.4f} {snr:>8.1f}")
    print(f"\nPeaks at k = log p^2:")
    print(f"  {'p^2':>4} {'2log p':>10} {'k_peak':>10} {'|F|':>10} {'SNR':>8}")
    for pp, ke, kp, h in squares:
        snr = h / bg_median if bg_median > 0 else float("inf")
        print(f"  {pp:>4} {ke:>10.5f} {kp:>10.5f} {h:>10.4f} {snr:>8.1f}")

    # ---- Plot ----
    fig, ax = plt.subplots(figsize=(11, 5))
    ax.plot(k_grid, absF, lw=0.6, color="C0", label="|F(k)|")
    ymax = absF.max() * 1.05
    for p in PRIMES_SMALL:
        ax.axvline(np.log(p), color="C3", ls="--", lw=0.6, alpha=0.7)
        ax.text(np.log(p), ymax * 0.92, f"log {p}", fontsize=7,
                ha="center", color="C3",
                bbox=dict(boxstyle="round,pad=0.1", fc="white", ec="none", alpha=0.8))
    for pp, ke, _, _ in squares:
        ax.axvline(ke, color="C2", ls=":", lw=0.5, alpha=0.6)
    ax.axhline(bg_median, color="gray", ls="-", lw=0.5, alpha=0.7,
               label=f"bg median={bg_median:.3f}")
    ax.set_xlim(0, 10)
    ax.set_ylim(0, ymax)
    ax.set_xlabel("k")
    ax.set_ylabel("|F(k)|")
    ax.set_title(f"Riemann-zero Fourier sum, N={N}.  Red: log p; Green: log p^2.")
    ax.legend(loc="upper right", fontsize=8)
    fig.tight_layout()
    plot_path = os.path.join(HERE, "riemann_quasicrystal.png")
    fig.savefig(plot_path, dpi=140)
    print(f"\nPlot saved to {plot_path}")

    # Data dump for the table in the writeup
    print("\nMarkdown table (for report):")
    print("| p  | log p   | k_peak  | |F(log p)| | SNR  |")
    print("|----|---------|---------|-----------|------|")
    for p, ke, kp, h in rows:
        snr = h / bg_median if bg_median > 0 else float("inf")
        print(f"| {p:<2} | {ke:.5f} | {kp:.5f} | {h:.4f}    | {snr:.1f} |")


if __name__ == "__main__":
    main()
