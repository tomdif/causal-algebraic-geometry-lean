"""
Rainbow 5: Dimensional Gap Ladder.

Strategy: Transfer matrix eigenvector approach only (brute force too slow).
For d=2: state = (lo, hi), 0 ≤ lo ≤ hi < m.
For d=3: state = (a, b), a,b nonincreasing on {0,...,m-1} → {0,...,m-1}, a≤b somewhere.
"""
import numpy as np
from scipy.linalg import eigh
from scipy.sparse import lil_matrix
from scipy.sparse.linalg import eigsh
import time

def enum_noninc(m, length):
    """Enumerate nonincreasing functions {0,...,length-1} → {0,...,m-1}."""
    if length == 0:
        return [()]
    if length == 1:
        return [(v,) for v in range(m)]
    result = []
    for first in range(m):
        for s in enum_noninc(first + 1, length - 1):
            result.append((first,) + s)
    return result

def gap_d2(m):
    """d=2 transfer matrix gap."""
    states = [(lo, hi) for lo in range(m) for hi in range(lo, m)]
    n = len(states)
    widths = np.array([hi - lo + 1 for lo, hi in states], dtype=float)

    T = np.zeros((n, n))
    for i, (lo1, hi1) in enumerate(states):
        for j, (lo2, hi2) in enumerate(states):
            if lo2 <= lo1 and hi2 <= hi1:
                T[i, j] = 1.0

    T_sym = (T + T.T) / 2.0
    evals, evecs = eigh(T_sym, subset_by_index=[n-1, n-1])
    psi2 = evecs[:, 0]**2
    psi2 /= psi2.sum()
    return np.dot(psi2, widths) / m

def gap_d3(m):
    """d=3 transfer matrix gap."""
    t0 = time.time()
    noninc = enum_noninc(m, m)
    nf = len(noninc)
    print(f"    {nf} noninc functions", end="")

    states = []
    volumes = []
    for a in noninc:
        for b in noninc:
            vol = sum(max(0, b[j] - a[j] + 1) for j in range(m))
            if vol > 0:
                states.append((a, b))
                volumes.append(vol)

    n = len(states)
    volumes = np.array(volumes, dtype=float)
    print(f", {n} states", end="")

    if n > 15000:
        print(f" — too large, skipping")
        return None, None

    # Build transfer matrix
    T = np.zeros((n, n), dtype=np.float32)
    for i, (a1, b1) in enumerate(states):
        for j, (a2, b2) in enumerate(states):
            ok = True
            for k in range(m):
                if a2[k] > a1[k] or b2[k] > b1[k]:
                    ok = False
                    break
            if ok:
                T[i, j] = 1.0

    t1 = time.time()

    T_sym = (T + T.T) / 2.0
    evals, evecs = eigh(T_sym.astype(np.float64), subset_by_index=[n-1, n-1])
    psi2 = evecs[:, 0]**2
    psi2 /= psi2.sum()
    avg_vol = np.dot(psi2, volumes)
    gap = avg_vol / m**2

    t2 = time.time()
    print(f" → gap={gap:.6f}, λ={evals[0]:.2f} [{t1-t0:.1f}s+{t2-t1:.1f}s]")
    return gap, evals[0]

# ==================== d=2 ====================
print("d=2 (transfer matrix, symmetrized eigenvector)")
print("-" * 50)
gaps_2 = []
ms_2 = list(range(3, 50))
for m in ms_2:
    g = gap_d2(m)
    gaps_2.append(g)
    print(f"  m={m:3d}: gap={g:.8f}")

# Extrapolate d=2
from numpy.linalg import lstsq
ms_fit = np.array(ms_2[-20:], dtype=float)
gs_fit = np.array(gaps_2[-20:])
A = np.column_stack([np.ones(len(ms_fit)), 1/ms_fit, 1/ms_fit**2])
coeff = lstsq(A, gs_fit, rcond=None)[0]
print(f"\n  Extrapolated γ₂(∞) = {coeff[0]:.8f}")
print(f"  (known: 0.27641374)")

# ==================== d=3 ====================
print(f"\nd=3 (transfer matrix, symmetrized eigenvector)")
print("-" * 50)
gaps_3 = []
ms_3 = []
for m in range(2, 8):
    print(f"  m={m}: ", end="")
    g, lam = gap_d3(m)
    if g is not None:
        gaps_3.append(g)
        ms_3.append(m)

if len(ms_3) >= 3:
    ms_fit3 = np.array(ms_3[-min(5,len(ms_3)):], dtype=float)
    gs_fit3 = np.array(gaps_3[-min(5,len(gaps_3)):])
    A3 = np.column_stack([np.ones(len(ms_fit3)), 1/ms_fit3, 1/ms_fit3**2])
    coeff3 = lstsq(A3, gs_fit3, rcond=None)[0]
    print(f"\n  Extrapolated γ₃(∞) = {coeff3[0]:.8f}")

# ==================== Summary ====================
print(f"\n{'='*50}")
print(f"DIMENSIONAL GAP LADDER (from transfer matrix)")
print(f"{'='*50}")
print(f"  γ₂(∞) ≈ {coeff[0]:.6f} (known: 0.276414)")
if len(ms_3) >= 3:
    print(f"  γ₃(∞) ≈ {coeff3[0]:.6f}")
    print(f"  γ₃/γ₂ ≈ {coeff3[0]/coeff[0]:.4f}")
