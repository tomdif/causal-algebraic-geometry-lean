#!/usr/bin/env python3
"""
rainbow_e_trace_ratio.py — THE critical test

Does tr_even / tr_odd → (d+1)/(d-1) for general d?

If YES: the trace ratio forces the eigenvalue ratio (via spectral concentration),
and the Dimensional Eigenvalue Law has an algebraic proof route.

If NO: the eigenvalue ratio and trace ratio differ, and the law is purely spectral.
"""

import numpy as np
from itertools import permutations, combinations
from math import comb

def sign_of_perm(p):
    n = len(p)
    inv = sum(1 for i in range(n) for j in range(i+1,n) if p[i] > p[j])
    return (-1)**inv

def chamber_traces(m, d):
    """Compute tr(K) and tr(RK) for the d-dimensional chamber kernel."""
    states = list(combinations(range(m), d))
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}

    perms = list(permutations(range(d)))
    perm_signs = [sign_of_perm(p) for p in perms]

    # tr(K) = Σ_P K_F(P,P)
    tr_K = 0
    tr_RK = 0
    for P in states:
        # K_F(P,P) = Σ_σ sign(σ) [comparable(P, σP)]
        kpp = 0
        for perm, sgn in zip(perms, perm_signs):
            Pp = tuple(P[perm[i]] for i in range(d))
            if all(P[i] <= Pp[i] for i in range(d)) or \
               all(Pp[i] <= P[i] for i in range(d)):
                kpp += sgn
        tr_K += kpp

        # R(P) = (m-1-P[d-1], ..., m-1-P[0])
        RP = tuple(m - 1 - P[d-1-j] for j in range(d))
        # K_F(R(P), P) = Σ_σ sign(σ) [comparable(RP, σP)]
        krpp = 0
        for perm, sgn in zip(perms, perm_signs):
            Pp = tuple(P[perm[i]] for i in range(d))
            if all(RP[i] <= Pp[i] for i in range(d)) or \
               all(Pp[i] <= RP[i] for i in range(d)):
                krpp += sgn
        tr_RK += krpp

    tr_even = (tr_K + tr_RK) / 2
    tr_odd = (tr_K - tr_RK) / 2

    return {
        'm': m, 'd': d, 'n': n,
        'tr_K': tr_K, 'tr_RK': tr_RK,
        'tr_even': tr_even, 'tr_odd': tr_odd,
        'tr_ratio': tr_even / tr_odd if tr_odd != 0 else float('inf'),
    }

print("=" * 95)
print("THE CRITICAL TEST: Does tr_even/tr_odd → (d+1)/(d-1)?")
print("=" * 95)

for d in [2, 3, 4, 5]:
    target = (d+1)/(d-1)
    print(f"\n### d={d}: Target = ({d+1})/({d-1}) = {target:.6f}")
    print(f"{'m':>3} {'n':>6} {'tr_K':>8} {'tr_RK':>8} {'tr_e':>8} {'tr_o':>8} "
          f"{'tr_e/tr_o':>10} {'target':>10} {'diff':>10}")

    results = []
    for m in range(d+1, 30):
        n_states = comb(m, d)
        if n_states > 5000:
            break
        r = chamber_traces(m, d)
        if r['tr_odd'] == 0:
            print(f"{m:3d} {r['n']:6d} {r['tr_K']:8.0f} {r['tr_RK']:8.0f} "
                  f"{r['tr_even']:8.1f} {r['tr_odd']:8.1f} {'inf':>10} {target:10.6f} {'---':>10}")
            continue
        results.append(r)
        diff = r['tr_ratio'] - target
        print(f"{m:3d} {r['n']:6d} {r['tr_K']:8.0f} {r['tr_RK']:8.0f} "
              f"{r['tr_even']:8.1f} {r['tr_odd']:8.1f} {r['tr_ratio']:10.5f} "
              f"{target:10.6f} {diff:10.5f}")

    if len(results) >= 4:
        # Check: does it converge or stay constant?
        even_m = [r for r in results if r['m'] % 2 == 0]
        odd_m = [r for r in results if r['m'] % 2 == 1]
        if even_m:
            vals = [f'{r["tr_ratio"]:.4f}' for r in even_m[-4:]]
            print(f"  Even m tail: {vals}")
        if odd_m:
            vals = [f'{r["tr_ratio"]:.4f}' for r in odd_m[-4:]]
            print(f"  Odd m tail:  {vals}")

# ============================================================
# Focus: d=3 trace identity structure
# ============================================================
print("\n" + "=" * 95)
print("d=3 TRACE IDENTITY: looking for the pattern in tr(RK)")
print("=" * 95)

print(f"\n{'m':>3} {'tr_K':>8} {'tr_RK':>8} {'C(m,3)':>8} {'tr_RK guess':>12}")
for m in range(4, 20):
    n_states = comb(m, 3)
    if n_states > 5000:
        break
    r = chamber_traces(m, 3)
    # Try various formulas for tr_RK
    half = m // 2
    # Guess: C(⌊m/2⌋, 2) or ⌊m/2⌋^3 or ...
    guess1 = comb(half, 2)  # triangular number of half
    guess2 = half ** 3
    guess3 = comb(half, 3)
    guess4 = half * (half - 1) * (half - 2) // 6 if half >= 3 else 0  # same as C(half,3)
    guess5 = half * comb(half, 2)  # half * C(half,2)
    # What about ⌊m/2⌋ · ⌊(m-1)/2⌋?
    half2 = (m-1) // 2
    guess6 = half * half2
    guess7 = comb(half + 1, 3)

    print(f"{m:3d} {r['tr_K']:8.0f} {r['tr_RK']:8.0f} {n_states:8d}  "
          f"C(h,2)={guess1:4d} h³={guess2:5d} C(h,3)={guess3:4d} "
          f"C(h+1,3)={guess7:4d} h·C(h,2)={guess5:5d}")

# Direct search: what IS the formula for tr_RK in d=3?
print("\nd=3 tr(RK) values:")
trRK_vals = []
for m in range(4, 20):
    if comb(m, 3) > 5000:
        break
    r = chamber_traces(m, 3)
    trRK_vals.append((m, int(r['tr_RK'])))
    print(f"  m={m:2d}: tr(RK) = {int(r['tr_RK']):5d}")

# Try OEIS-style: look at the sequence
print("\ntr(RK) sequence for d=3:", [v for _,v in trRK_vals])

# Check: is it ⌊m/2⌋ * ⌊(m-1)/2⌋ * ⌊(m-2)/2⌋ / 6 or similar?
print("\nPattern test:")
for m, trRK in trRK_vals:
    a = m // 2
    b = (m-1) // 2
    c = (m-2) // 2
    test1 = a * b  # for d=2 this was ⌊m/2⌋²
    test2 = a * b * c
    test3 = a ** 2 * b
    # d=2 formula: ⌊m/2⌋² = (m//2)^2. For d=3, natural guess: (m//2)^3?
    # But m=4: (2)^3=8≠2, m=5: (2)^3=8≠6. No.
    # What about C(⌊m/2⌋,2)?
    test4 = comb(a, 2)
    # ⌊m/2⌋·⌊(m+1)/2⌋·⌊(m-1)/2⌋?
    d2 = (m+1)//2
    test5 = a * d2
    print(f"  m={m:2d}: tr(RK)={trRK:4d}  ⌊m/2⌋²·⌊(m-2)/2⌋={a**2*c:5d}  "
          f"(m//2)·((m-1)//2)={test1:4d}  C(⌊m/2⌋,2)={test4:4d}  "
          f"⌊m/2⌋·⌊(m+1)/2⌋={test5:4d}")

# ============================================================
# d=2 reference: tr(RK) = ⌊m/2⌋² and tr_e/tr_o → 3
# ============================================================
print("\n" + "=" * 95)
print("REFERENCE: d=2 trace ratio behavior (oscillation pattern)")
print("=" * 95)
print(f"{'m':>3} {'tr_e/tr_o':>10} {'(d+1)/(d-1)':>12} {'diff':>10}")
for m in range(4, 25):
    r = chamber_traces(m, 2)
    if r['tr_odd'] != 0:
        print(f"{m:3d} {r['tr_ratio']:10.5f} {3.0:12.5f} {r['tr_ratio']-3:10.5f}")
