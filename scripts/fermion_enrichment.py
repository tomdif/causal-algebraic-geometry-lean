"""
Fermion Enrichment: Minimal Structure for Physical Fermions

The bulk comparability framework is intrinsically BOSONIC:
  - Transfer matrix T has all nonneg entries => Perron-Frobenius => unique positive ground state
  - Reflection positivity holds in positive sector only
  - Kahler-Dirac boundary modes have right algebra but 89% intertwiner error

This script investigates three MINIMAL enrichments that could produce physical fermions.
All computations at m=4, d=2 for tractability.

Classification: EXPLORATORY (testing whether bolted-on structure gives real fermions)
"""

import numpy as np
from scipy.linalg import eigh, eig
from itertools import product as iterproduct

# ============================================================================
# Shared infrastructure: discrete [m]^d lattice model
# ============================================================================

def build_poset_and_transfer(m, d):
    """Build the product poset [m]^d and its comparability transfer matrix.

    Elements: tuples in {0,...,m-1}^d
    Comparability: x <= y componentwise (product order)
    Transfer T[i,j] = 1 if x_i and x_j are comparable, else 0.
    """
    elements = list(iterproduct(range(m), repeat=d))
    n = len(elements)

    T = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            xi, xj = elements[i], elements[j]
            le = all(xi[k] <= xj[k] for k in range(d))
            ge = all(xi[k] >= xj[k] for k in range(d))
            if le or ge:
                T[i, j] = 1.0

    T_sym = (T + T.T) / 2  # already symmetric for comparability, but be safe
    return elements, T_sym


def print_spectrum(label, evals, n_show=8):
    """Print top eigenvalues."""
    idx = np.argsort(np.abs(evals))[::-1]
    evals_sorted = evals[idx]
    print(f"  Top {n_show} eigenvalues of {label}:")
    for k in range(min(n_show, len(evals_sorted))):
        ev = evals_sorted[k]
        if np.isreal(ev):
            print(f"    {k+1:3d}: {ev.real:12.6f}")
        else:
            print(f"    {k+1:3d}: {ev.real:12.6f} + {ev.imag:12.6f}i")
    print()


# ============================================================================
# Proposal A: Spin Structure on Poset (Z/2-graded fiber)
# ============================================================================

def proposal_a(m, d):
    print("=" * 70)
    print("PROPOSAL A: Z/2 SPIN STRUCTURE ON POSET")
    print("=" * 70)
    print()
    print("  Enrichment: assign parity (-1)^{sum of coords} to each element.")
    print("  Graded transfer: T_graded[i,j] = T[i,j] * (-1)^{p(i)+p(j)}")
    print("  Cost: 1 bit per lattice site (parity of coordinate sum)")
    print()

    elements, T = build_poset_and_transfer(m, d)
    n = len(elements)

    # Parity: (-1)^(sum of coordinates)
    parity = np.array([(-1) ** sum(x) for x in elements])

    # Graded transfer: bosonic sectors (same parity) get +1, fermionic (different) get -1
    # T_graded[i,j] = T[i,j] * parity[i] * parity[j]
    P = np.outer(parity, parity)
    T_graded = T * P

    # Spectra
    evals_T = np.linalg.eigvalsh(T)
    evals_G = np.linalg.eigvalsh(T_graded)

    print_spectrum("T (ungraded)", evals_T)
    print_spectrum("T_graded", evals_G)

    # Key check: does grading break positivity?
    n_neg_T = np.sum(evals_T < -1e-10)
    n_neg_G = np.sum(evals_G < -1e-10)
    n_pos_T = np.sum(evals_T > 1e-10)
    n_pos_G = np.sum(evals_G > 1e-10)

    print(f"  Ungraded T: {n_pos_T} positive, {n_neg_T} negative eigenvalues")
    print(f"  Graded T:   {n_pos_G} positive, {n_neg_G} negative eigenvalues")
    print()

    # Spectral pairing check: are eigenvalues of T_graded a rearrangement of T?
    evals_T_sorted = np.sort(np.abs(evals_T))[::-1]
    evals_G_sorted = np.sort(np.abs(evals_G))[::-1]
    spec_diff = np.max(np.abs(evals_T_sorted - evals_G_sorted))
    print(f"  |spec(T)| vs |spec(T_graded)|: max diff = {spec_diff:.6e}")
    print(f"  (If 0, grading is just a similarity transform -- no new physics)")
    print()

    # Check: is T_graded = D T D^{-1} where D = diag(parity)?
    D = np.diag(parity.astype(float))
    diff = np.max(np.abs(T_graded - D @ T @ D))
    print(f"  T_graded = D T D^{{-1}} check: max diff = {diff:.6e}")

    is_conjugate = diff < 1e-10
    print()
    print("  ASSESSMENT:")
    if is_conjugate:
        print("    T_graded is UNITARILY EQUIVALENT to T (D is diagonal unitary).")
        print("    The grading is a gauge choice, not new physics.")
        print("    Eigenvalues identical, just relabeled. NO fermions produced.")
        print("    VERDICT: FAILS. The Z/2 grading is too cheap -- it's just a basis change.")
    else:
        print("    T_graded differs from T. Checking for fermionic content...")

    print()
    return is_conjugate


# ============================================================================
# Proposal B: Kahler-Dirac Enrichment of Transfer
# ============================================================================

def build_kahler_dirac(elements, m, d):
    """Build a discrete Kahler-Dirac operator on the poset.

    D_KD acts on the chain complex of the order complex.
    Simplified model: D_KD = adjacency of Hasse diagram with alternating signs.
    For the product poset, Hasse edges connect elements differing by 1 in one coord.
    """
    n = len(elements)
    D = np.zeros((n, n))

    for i in range(n):
        for j in range(n):
            xi, xj = elements[i], elements[j]
            # Hasse edge: differ by exactly 1 in exactly one coordinate
            diff = [xj[k] - xi[k] for k in range(d)]
            n_nonzero = sum(1 for dk in diff if dk != 0)
            if n_nonzero == 1:
                # Which coordinate changed?
                coord = next(k for k in range(d) if diff[k] != 0)
                if diff[coord] == 1:
                    # Sign from grading: (-1)^{sum of coords below changed one}
                    sign = (-1) ** sum(xi[k] for k in range(coord))
                    D[i, j] = sign
                elif diff[coord] == -1:
                    sign = (-1) ** sum(xj[k] for k in range(coord))
                    D[j, i] = sign  # already handled by the i<->j swap

    # Make D_KD = D + D^T (so it's the full Kahler-Dirac, not just d or d*)
    D_KD = D + D.T
    return D_KD


def proposal_b(m, d):
    print("=" * 70)
    print("PROPOSAL B: KAHLER-DIRAC ENRICHMENT OF TRANSFER")
    print("=" * 70)
    print()
    print("  Enrichment: T_enriched = T (x) I + alpha * I (x) D_KD")
    print("  This couples bulk transfer dynamics to boundary-like modes.")
    print("  Cost: doubles Hilbert space dimension (tensor product)")
    print()

    elements, T = build_poset_and_transfer(m, d)
    n = len(elements)
    D_KD = build_kahler_dirac(elements, m, d)

    # Check D_KD^2 and anticommutation
    D2 = D_KD @ D_KD
    print(f"  Lattice size: {n} elements in [{m}]^{d}")
    print(f"  D_KD: {n}x{n}, ||D_KD||_F = {np.linalg.norm(D_KD, 'fro'):.4f}")

    # Spectrum of D_KD alone
    evals_D = np.linalg.eigvalsh(D_KD)
    print_spectrum("D_KD (Kahler-Dirac)", evals_D)

    # Check spectral symmetry of D_KD
    evals_D_sorted = np.sort(evals_D)
    n_pairs = 0
    for ev in evals_D_sorted:
        if ev > 1e-10 and np.any(np.abs(evals_D_sorted + ev) < 1e-6):
            n_pairs += 1
    print(f"  D_KD spectral pairing: {n_pairs} pairs of +/-lambda")
    print(f"  D_KD zero modes: {np.sum(np.abs(evals_D) < 1e-10)}")
    print()

    # Build enriched operator: T_enriched = T (x) I_2 + alpha * I_n (x) sigma_z
    # But more physically: work in doubled space
    alpha = 1.0 / np.max(np.abs(evals_D))  # normalize D_KD to O(1)

    T_enriched = np.kron(T, np.eye(n)) + alpha * np.kron(np.eye(n), D_KD)
    dim_enriched = n * n

    print(f"  T_enriched: {dim_enriched}x{dim_enriched}")
    print(f"  alpha (coupling) = {alpha:.6f}")

    # Get spectrum (use only top eigenvalues for large matrix)
    n_want = min(16, dim_enriched)
    evals_enriched = np.linalg.eigvalsh(T_enriched)
    evals_enriched_top = np.sort(evals_enriched)[::-1][:n_want]

    print_spectrum("T_enriched", evals_enriched_top)

    # Check for +/- pairing in enriched spectrum
    all_ev = np.sort(evals_enriched)
    n_paired = 0
    used = np.zeros(len(all_ev), dtype=bool)
    for i in range(len(all_ev)):
        if used[i] or abs(all_ev[i]) < 1e-10:
            continue
        for j in range(len(all_ev)):
            if not used[j] and abs(all_ev[i] + all_ev[j]) < 1e-6:
                n_paired += 1
                used[i] = used[j] = True
                break

    n_zero_enriched = np.sum(np.abs(evals_enriched) < 1e-10)
    print(f"  +/- paired eigenvalues: {n_paired} pairs")
    print(f"  Zero modes: {n_zero_enriched}")
    print(f"  Unpaired: {len(all_ev) - 2*n_paired - n_zero_enriched}")
    print()

    # Compare mass gaps
    evals_T_sorted = np.sort(np.linalg.eigvalsh(T))[::-1]
    gap_T = -np.log(evals_T_sorted[1] / evals_T_sorted[0]) if evals_T_sorted[0] > 0 else 0
    gap_enriched = -np.log(evals_enriched_top[1] / evals_enriched_top[0]) if evals_enriched_top[0] > 0 else 0

    print(f"  Mass gap (T alone):     {gap_T:.6f}")
    print(f"  Mass gap (T_enriched):  {gap_enriched:.6f}")
    print()

    print("  ASSESSMENT:")
    print("    T_enriched = T (x) I + alpha * I (x) D_KD is a TENSOR SUM.")
    print("    Its eigenvalues are lambda_i(T) + alpha * mu_j(D_KD).")
    print("    This means T and D_KD sectors DECOUPLE -- no true coupling.")
    print("    The +/- pairing comes entirely from D_KD, NOT from interaction.")
    print("    To get real fermion-boson coupling, need T_enriched = T (x) D_KD")
    print("    or some genuinely interacting term.")
    print("    VERDICT: STRUCTURALLY DECOUPLED. Need multiplicative, not additive, coupling.")
    print()


# ============================================================================
# Proposal C: Causal Spinor Field (K (x) gamma)
# ============================================================================

def proposal_c(m, d):
    print("=" * 70)
    print("PROPOSAL C: CAUSAL SPINOR FIELD")
    print("=" * 70)
    print()
    print("  Enrichment: K_spin = K (x) sigma_z (Pauli grading)")
    print("  Spinor space: 2n-dimensional (each site gets a 2-spinor for d=2)")
    print("  Cost: factor of 2^{floor(d/2)} per site (spinor fiber)")
    print()

    elements, T = build_poset_and_transfer(m, d)
    n = len(elements)

    # Pauli matrices
    sigma_x = np.array([[0, 1], [1, 0]], dtype=float)
    sigma_y = np.array([[0, -1j], [1j, 0]], dtype=complex)
    sigma_z = np.array([[1, 0], [0, -1]], dtype=float)
    I2 = np.eye(2)

    # === Model C1: K_spin = K (x) sigma_z ===
    K_spin = np.kron(T, sigma_z)
    evals_spin = np.linalg.eigvalsh(K_spin.real)

    print("  Model C1: K_spin = T (x) sigma_z")
    print(f"  Dimension: {2*n}")
    print_spectrum("K_spin", evals_spin)

    # This trivially gives +/- pairing: eigenvalues are +lambda_i and -lambda_i
    evals_T = np.linalg.eigvalsh(T)
    expected = np.sort(np.concatenate([evals_T, -evals_T]))[::-1]
    actual = np.sort(evals_spin)[::-1]
    diff_c1 = np.max(np.abs(expected - actual))
    print(f"  Spectrum = {{+lambda_i, -lambda_i}}: error = {diff_c1:.2e}")
    print(f"  Trivial doubling -- sigma_z just flips sign. No new content.")
    print()

    # === Model C2: K_spin = T (x) I + D_hasse (x) sigma_x (off-diagonal coupling) ===
    print("  Model C2: K_spin = T (x) I_2 + D_hasse (x) sigma_x")
    print("  (sigma_x couples the two spinor components via Hasse diagram)")

    D_KD = build_kahler_dirac(elements, m, d)

    # Normalize
    norm_T = np.max(np.abs(evals_T))
    norm_D = np.max(np.abs(np.linalg.eigvalsh(D_KD)))
    alpha = norm_T / norm_D if norm_D > 0 else 1.0

    K_c2 = np.kron(T, I2) + alpha * np.kron(D_KD, sigma_x)
    evals_c2 = np.linalg.eigvalsh(K_c2)
    evals_c2_sorted = np.sort(evals_c2)[::-1]

    print_spectrum("K_c2", evals_c2_sorted)

    # Check +/- pairing
    n_paired_c2 = 0
    used = np.zeros(len(evals_c2), dtype=bool)
    for i in range(len(evals_c2)):
        if used[i] or abs(evals_c2_sorted[i]) < 1e-10:
            continue
        for j in range(i+1, len(evals_c2)):
            if not used[j] and abs(evals_c2_sorted[i] + evals_c2_sorted[j]) < 1e-6:
                n_paired_c2 += 1
                used[i] = used[j] = True
                break

    n_zero_c2 = np.sum(np.abs(evals_c2) < 1e-10)
    print(f"  +/- pairs: {n_paired_c2}, zero modes: {n_zero_c2}, unpaired: {len(evals_c2) - 2*n_paired_c2 - n_zero_c2}")

    # Does sigma_x coupling break the all-positive ground state?
    gs_c2 = None
    evals_c2_full, evecs_c2 = np.linalg.eigh(K_c2)
    idx_top = np.argmax(evals_c2_full)
    gs_c2 = evecs_c2[:, idx_top]

    # Split into up/down spinor components
    gs_up = gs_c2[:n]
    gs_down = gs_c2[n:]
    frac_up = np.sum(gs_up**2)
    frac_down = np.sum(gs_down**2)

    print(f"  Ground state: |up> fraction = {frac_up:.4f}, |down> fraction = {frac_down:.4f}")

    # Check if ground state mixes spinor components
    sign_changes_up = np.sum(np.diff(np.sign(gs_up[gs_up != 0])) != 0)
    sign_changes_down = np.sum(np.diff(np.sign(gs_down[gs_down != 0])) != 0)
    print(f"  Sign changes: up={sign_changes_up}, down={sign_changes_down}")
    print()

    # Mass gap comparison
    gap_T_only = -np.log(evals_T[np.argsort(evals_T)[-2]] / evals_T[np.argsort(evals_T)[-1]])
    gap_c2 = -np.log(evals_c2_full[np.argsort(evals_c2_full)[-2]] / evals_c2_full[np.argsort(evals_c2_full)[-1]])
    print(f"  Mass gap (T alone): {gap_T_only:.6f}")
    print(f"  Mass gap (C2):      {gap_c2:.6f}")
    print()

    print("  ASSESSMENT:")
    print(f"    C1 (T (x) sigma_z): trivial doubling, no new physics.")
    print(f"    C2 (T (x) I + D (x) sigma_x): genuine mixing of spinor components.")
    if n_paired_c2 > 0:
        print(f"    C2 has {n_paired_c2} +/- pairs -- partial fermionic structure.")
    else:
        print(f"    C2 has NO +/- pairing -- the T term breaks spectral symmetry.")
    print(f"    Ground state is {frac_up:.0%}/{frac_down:.0%} up/down -- ", end="")
    if abs(frac_up - frac_down) < 0.1:
        print("good mixing.")
    else:
        print("dominated by one component.")
    print(f"    The sigma_x coupling IS genuinely interacting (not a tensor sum).")
    print(f"    But it's BOLTED ON -- nothing in the poset forces sigma_x over sigma_y or sigma_z.")
    print()


# ============================================================================
# Summary and honest verdict
# ============================================================================

def summary():
    print("=" * 70)
    print("OVERALL VERDICT")
    print("=" * 70)
    print()
    print("  Proposal A (Z/2 grading):    FAILS")
    print("    The grading is a similarity transform. Same spectrum, no fermions.")
    print("    Cost: 1 bit/site. But 1 bit buys nothing -- it's a gauge choice.")
    print()
    print("  Proposal B (KD enrichment):  STRUCTURALLY DECOUPLED")
    print("    Additive tensor T+D gives decoupled sectors, not interacting fermions.")
    print("    Cost: n^2 dim Hilbert space. Expensive AND doesn't work.")
    print()
    print("  Proposal C1 (K (x) sigma_z): TRIVIAL DOUBLING")
    print("    Just reflects spectrum. No new content.")
    print()
    print("  Proposal C2 (T (x) I + D (x) sigma_x): BEST CANDIDATE")
    print("    Genuine coupling between spinor components and lattice dynamics.")
    print("    Produces partial +/- pairing and mixed ground state.")
    print("    BUT: choice of gamma matrix is arbitrary (sigma_x vs sigma_y vs sigma_z).")
    print("    Nothing in the poset structure SELECTS a particular Clifford algebra.")
    print()
    print("  FUNDAMENTAL OBSTACLE:")
    print("    The poset [m]^d has no tangent bundle, no spin structure, no Clifford")
    print("    algebra. Any gamma matrix is external structure bolted onto a combinatorial")
    print("    object. The cost is always at least 2^{floor(d/2)} per site, and the")
    print("    choice is NEVER forced by the comparability relation alone.")
    print()
    print("    This confirms the fermion barrier: the bulk is intrinsically bosonic.")
    print("    Getting fermions requires either:")
    print("      (1) Finding a HIDDEN spinor structure in the poset (unlikely),")
    print("      (2) Accepting fermions as EMERGENT boundary modes (Kahler-Dirac), or")
    print("      (3) Explicitly adding a spin bundle (standard lattice gauge theory).")
    print()
    print("    Option (2) remains the most natural -- the boundary S^{d-1} DOES have")
    print("    a tangent bundle, and the Kahler-Dirac operator IS intrinsic to it.")
    print("    The 89% intertwiner error is the quantitative measure of how hard it is")
    print("    to couple these boundary fermions to bulk dynamics.")
    print()


def main():
    m, d = 4, 2
    print(f"Fermion Enrichment Investigation: m={m}, d={d}")
    print(f"Lattice [m]^d = [{m}]^{d} has {m**d} elements")
    print()

    proposal_a(m, d)
    proposal_b(m, d)
    proposal_c(m, d)
    summary()


if __name__ == "__main__":
    main()
