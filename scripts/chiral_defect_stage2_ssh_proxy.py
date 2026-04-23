#!/usr/bin/env python3
"""
Stage 2 PROXY — 1D SSH soliton as a canonical A/B-sublattice test.

This is NOT a direct test of the K/P chamber-kernel hypothesis. It is a
pre-check that the Sharpe-style mechanism (A/B sublattice + topological
defect → spatially localized zero mode with chiral weight) works in a
canonical 1D setting. See docs/ChiralDefectStatus.md for why the real
K/P test requires extending the chamber-kernel framework to 2D causal
sets before a rigorous run is possible.

Hypothesis (this proxy):
  On the 1D SSH chain (A/B sublattice, alternating hoppings), a soliton
  (domain wall between two dimerization patterns) has a localized
  zero-energy eigenmode concentrated on one sublattice.

Expected outcome (KNOWN PHYSICS, SSH 1979):
  - Vacuum (uniform dimerization): two gapped bands, no zero mode.
  - Soliton: one exact zero mode, exponentially localized near the
    domain wall, living entirely on the A-sublattice (or entirely B,
    depending on which side wins).

If THIS fails, my numerical infrastructure has a bug. If it passes, the
mechanism is confirmed for A/B chains — and the next research task is
to determine whether K/P on causal-set chamber kernels has the same
sublattice-localization structure.
"""

import numpy as np

# SSH parameters. u = intra-dimer hop, v = inter-dimer hop.
# Topological: |v| > |u|.  Trivial: |u| > |v|.
U_TRIV = 1.0
V_TRIV = 0.5  # trivial phase
U_TOPO = 0.5
V_TOPO = 1.0  # topological phase
L_HALF = 60   # number of unit cells on each side of soliton (so 2*60*2 = 240 sites total)


def build_ssh_hamiltonian(u_pattern, v_pattern):
    """Build SSH Hamiltonian with explicit per-bond u_i (intra) and v_i (inter).

    Unit cell has 2 sites (A, B).  Intra-cell hopping: A_i <-> B_i (amp u_i).
    Inter-cell hopping: B_i <-> A_{i+1} (amp v_i).
    """
    n_cells = len(u_pattern)
    assert len(v_pattern) == n_cells - 1, "v has one fewer bond than cells"
    N = 2 * n_cells
    H = np.zeros((N, N))
    for i in range(n_cells):
        H[2*i, 2*i + 1] = u_pattern[i]
        H[2*i + 1, 2*i] = u_pattern[i]
    for i in range(n_cells - 1):
        H[2*i + 1, 2*(i+1)] = v_pattern[i]
        H[2*(i+1), 2*i + 1] = v_pattern[i]
    return H


def participation_ratio(v):
    """PR = (sum |v|^2)^2 / (N * sum |v|^4), in [1/N, 1]."""
    p = np.abs(v) ** 2
    p = p / p.sum()
    return 1.0 / (len(p) * np.sum(p ** 2))


def sublattice_weight(v):
    """Fraction of |v|^2 on even-indexed sites (A sublattice)."""
    p = np.abs(v) ** 2
    p = p / p.sum()
    return p[0::2].sum()


def run_vacuum():
    """Uniform TRIVIAL dimerization, open BC.  Trivial phase has no edge/zero modes
    (gap centered on E=0, no states inside).  |u| > |v|."""
    n_cells = 2 * L_HALF
    u = np.full(n_cells, U_TRIV)
    v = np.full(n_cells - 1, V_TRIV)
    H = build_ssh_hamiltonian(u, v)
    ev, V = np.linalg.eigh(H)
    idx_sorted = np.argsort(np.abs(ev))
    return {
        "three_smallest_abs_ev": ev[idx_sorted[:3]].tolist(),
        "gap_to_smallest": float(np.abs(ev[idx_sorted[1]]) - np.abs(ev[idx_sorted[0]])),
        "smallest_mode_PR": participation_ratio(V[:, idx_sorted[0]]),
        "smallest_mode_A_weight": sublattice_weight(V[:, idx_sorted[0]]),
    }


def run_soliton():
    """Dimerization inverts at center.

    Left half:  trivial  (u=1.0, v=0.5)
    Right half: topological (u=0.5, v=1.0)
    At the boundary the 'strong' inter-cell bond (v) persists on the right,
    and a free A-site at cell L_HALF becomes the domain-wall anchor.
    This is the classical Jackiw-Rebbi / Su-Schrieffer-Heeger soliton.
    """
    n_cells = 2 * L_HALF
    u = np.concatenate([np.full(L_HALF, U_TRIV), np.full(L_HALF, U_TOPO)])
    v_left = np.full(L_HALF - 1, V_TRIV)
    v_wall = [V_TRIV]  # boundary bond (inter-cell) between cell L-1 and cell L
    v_right = np.full(L_HALF - 1, V_TOPO)
    v = np.concatenate([v_left, v_wall, v_right])
    H = build_ssh_hamiltonian(u, v)
    ev, V = np.linalg.eigh(H)
    idx_sorted = np.argsort(np.abs(ev))
    v_zero = V[:, idx_sorted[0]]
    density = np.abs(v_zero) ** 2
    center = 2 * L_HALF  # site index of the domain-wall A-site
    return {
        "three_smallest_abs_ev": ev[idx_sorted[:3]].tolist(),
        "gap_to_next": float(np.abs(ev[idx_sorted[1]])),
        "zero_mode_PR": participation_ratio(v_zero),
        "zero_mode_A_weight": sublattice_weight(v_zero),
        "peak_site": int(np.argmax(density)),
        "soliton_site": center,
        "peak_density": float(density.max()),
        "peak_within_5_of_soliton": abs(int(np.argmax(density)) - center) <= 5,
        "density": density.tolist(),
    }


def N_to_site(total_sites, L_half):
    # Soliton is at the boundary between unit cells L_HALF - 1 and L_HALF,
    # which is roughly site 2*L_HALF - 1 or 2*L_HALF.
    return 2 * L_half - 1


def main():
    print("=" * 70)
    print("Stage 2 (PROXY) — SSH soliton A/B localization test")
    print("=" * 70)

    vac = run_vacuum()
    print(f"\nVacuum (uniform topological dimerization):")
    print(f"  three smallest |ev| = {vac['three_smallest_abs_ev']}")
    print(f"  smallest mode PR     = {vac['smallest_mode_PR']:.4f}")
    print(f"  smallest mode A-wt   = {vac['smallest_mode_A_weight']:.4f}")

    sol = run_soliton()
    print(f"\nSoliton (domain wall at cell {L_HALF}):")
    print(f"  three smallest |ev| = {sol['three_smallest_abs_ev']}")
    print(f"  zero-mode PR         = {sol['zero_mode_PR']:.4f}")
    print(f"  zero-mode A-weight   = {sol['zero_mode_A_weight']:.4f}")
    print(f"  peak site            = {sol['peak_site']} (soliton at {sol['soliton_site']})")
    print(f"  peak within 5 sites  = {sol['peak_within_5_of_soliton']}")

    # Pre-committed success criteria (proxy version):
    # 1. Vacuum smallest mode is NOT a zero mode (|ev| gapped > 0.1)
    # 2. Soliton has a true zero mode (|ev| < 1e-8)
    # 3. Zero-mode PR < 0.1 (localized)
    # 4. Zero-mode A-weight < 0.1 OR > 0.9 (chiral)
    # 5. Peak within 5 sites of soliton
    print("\n" + "=" * 70)
    print("Pre-committed proxy checks:")
    print("=" * 70)
    checks = []
    c1 = abs(vac["three_smallest_abs_ev"][0]) > 0.1
    checks.append(("vacuum has no zero mode (gap > 0.1)", c1))
    c2 = abs(sol["three_smallest_abs_ev"][0]) < 1e-8
    checks.append(("soliton has exact zero mode (< 1e-8)", c2))
    c3 = sol["zero_mode_PR"] < 0.1
    checks.append(("zero mode localized (PR < 0.1)", c3))
    c4 = (sol["zero_mode_A_weight"] < 0.1) or (sol["zero_mode_A_weight"] > 0.9)
    checks.append(("zero mode chiral (A-weight < 0.1 or > 0.9)", c4))
    c5 = sol["peak_within_5_of_soliton"]
    checks.append(("peak within 5 sites of soliton", c5))

    for desc, ok in checks:
        print(f"  {'PASS' if ok else 'FAIL'}  {desc}")

    all_pass = all(ok for _, ok in checks)
    print(f"\nProxy OVERALL: {'PASS' if all_pass else 'FAIL'}")
    print("\nInterpretation:")
    if all_pass:
        print("  Known-physics mechanism confirmed on A/B chain.")
        print("  Next research task: determine whether K/P chamber-kernel")
        print("  on causal sets has analogous sublattice structure.")
        print("  This proxy does NOT yet validate H on causal substrate.")
    else:
        print("  Bug in infrastructure or chosen parameters; investigate before")
        print("  interpreting any downstream result.")

    return 0 if all_pass else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
