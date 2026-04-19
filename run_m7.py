"""Launch m=7 computation. Same as exact_3d_parallel but only does m=7."""
import sys
sys.path.insert(0, '/Users/thomasdifiore/causal-algebraic-geometry-lean')
from exact_3d_parallel import exact_count_3d_parallel
import time
from math import log
import numpy as np

if __name__ == '__main__':
    print("=== m=7 Computation ===\n")
    t0 = time.time()
    c7 = exact_count_3d_parallel(7)
    dt = time.time() - t0
    rho = c7 ** (1.0 / 49)
    print(f"\n|CC([7]³)| = {c7}")
    print(f"|CC|^{{1/49}} = {rho:.6f}")
    print(f"Time: {dt:.1f}s ({dt/60:.1f} min)\n")

    # Full fit with 6 data points
    vals = {
        2: 101,
        3: 129535,
        4: 4664028094,
        5: 4725549877891433,
        6: 148012683139998036804694,
        7: c7,
    }

    ms = np.array(list(vals.keys()), dtype=float)
    log_cc = np.array([log(v) for v in vals.values()])

    print("=== FIT WITH 6 DATA POINTS ===\n")

    # Quadratic
    A1 = np.vstack([ms**2, ms, np.ones(6)]).T
    c1 = np.linalg.lstsq(A1, log_cc, rcond=None)[0]
    resid1 = log_cc - A1 @ c1
    print(f"M1 (quadratic): {c1[0]:.6f}·m² + {c1[1]:.6f}·m + {c1[2]:.4f}")
    print(f"  ρ₃ = {np.exp(c1[0]):.6f}, RSS = {np.sum(resid1**2):.4e}")

    # Quadratic + log(m)
    A2 = np.vstack([ms**2, ms, np.log(ms), np.ones(6)]).T
    c2 = np.linalg.lstsq(A2, log_cc, rcond=None)[0]
    resid2 = log_cc - A2 @ c2
    print(f"\nM2 (+log): {c2[0]:.6f}·m² + {c2[1]:.6f}·m + {c2[2]:.4f}·log(m) + {c2[3]:.4f}")
    print(f"  ρ₃ = {np.exp(c2[0]):.6f}")
    print(f"  Log coefficient: {c2[2]:.6f}")
    print(f"  RSS = {np.sum(resid2**2):.4e}")

    # Full polynomial expansion with 1/m term
    A3 = np.vstack([ms**2, ms, np.log(ms), np.ones(6), 1/ms]).T
    c3 = np.linalg.lstsq(A3, log_cc, rcond=None)[0]
    resid3 = log_cc - A3 @ c3
    print(f"\nM3 (+1/m): a·m² + b·m + c·log(m) + d + e/m")
    print(f"  a={c3[0]:.6f}, b={c3[1]:.6f}, c={c3[2]:.4f}, d={c3[3]:.4f}, e={c3[4]:.4f}")
    print(f"  ρ₃ = {np.exp(c3[0]):.6f}")
    print(f"  RSS = {np.sum(resid3**2):.4e}")

    print("\n=== ρ_m convergence ===")
    for m, v in vals.items():
        print(f"  m={m}: |CC|^{{1/m²}} = {v ** (1.0/m**2):.6f}")
