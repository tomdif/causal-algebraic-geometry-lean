"""Asymptotic analysis of Q(m) = #{full-support antitone pairs on [m]²}."""
import math
import numpy as np

# Data from count_full_support_pairs_tm.py
Q = {1: 1, 2: 20, 3: 8790, 4: 89613429, 5: 21493411201893}
PP = {1: 2, 2: 20, 3: 980, 4: 232848, 5: 267227532}

L3 = 4.5 * math.log(3) - 6 * math.log(2)
print(f"L_3  = {L3:.6f}")
print(f"2L_3 = {2 * L3:.6f}  (conjectured target for log Q/m²)")
print()

# Table
print(f"{'m':>2} {'Q(m)':>16} {'lnQ/m²':>9} {'lnPP/m²':>9} {'Q/PP²':>12} {'ln(Q/PP²)':>11}")
for m in sorted(Q):
    lnQ = math.log(Q[m])
    lnPP = math.log(PP[m])
    ratio = Q[m] / PP[m] ** 2
    print(f"{m:>2} {Q[m]:>16} {lnQ/m**2:>9.4f} {lnPP/m**2:>9.4f} "
          f"{ratio:>12.6g} {math.log(ratio):>11.4f}")

# Fit ln(Q/PP²) = α + β·m  (geometric decay in m)
ms = np.array([m for m in sorted(Q) if m >= 2], dtype=float)
ys = np.array([math.log(Q[m] / PP[m]**2) for m in sorted(Q) if m >= 2])
A = np.vstack([np.ones_like(ms), ms]).T
alpha, beta = np.linalg.lstsq(A, ys, rcond=None)[0]
print(f"\nLinear fit  ln(Q/PP²) ≈ {alpha:.4f} + {beta:.4f}·m")
print(f"→ Q(m) ~ PP(m)² · exp({beta:+.4f}·m) · exp({alpha:+.4f})")
print(f"→ log Q(m)/m² = 2 log PP(m)/m² + β/m + α/m² → 2 L_3 as m→∞")
print()

# Fit log Q/m² = L + a/m + b/m²
xs = np.array(sorted(Q)[1:])  # skip m=1 boundary
ys2 = np.array([math.log(Q[m])/m**2 for m in sorted(Q) if m >= 2])
A2 = np.vstack([np.ones_like(xs, dtype=float), 1.0/xs, 1.0/xs**2]).T
L_fit, a_fit, b_fit = np.linalg.lstsq(A2, ys2, rcond=None)[0]
print(f"LS fit log Q/m² ≈ {L_fit:.4f} + {a_fit:.3f}/m + {b_fit:.3f}/m²")
print(f"Compare to 2 L_3 = {2*L3:.4f}")
print(f"Gap: {L_fit - 2*L3:+.4f}  ({100*(L_fit-2*L3)/(2*L3):+.2f}%)")
