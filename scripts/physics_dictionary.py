"""
Physics Dictionary: Complete Theory-to-Physics Translation

Compiles the full dictionary mapping mathematical objects in the
causal algebraic geometry framework to their physical analogs,
with honest status labels:

  DERIVABLE   = follows from the mathematics without additional assumptions
  STRUCTURAL  = correct structural match but requires interpretation
  SPECULATIVE = requires unproven assumptions or extrapolation
"""

# ============================================================
# The dictionary
# ============================================================

dictionary = [
    # --- DERIVABLE: follows from the math ---
    {
        "theory_object": "Transfer eigenvalue lambda_1",
        "physical_analog": "exp(-E_ground)",
        "status": "DERIVABLE",
        "numerical_value": "0.1746",
        "evidence": "Galerkin eigenvalue, converged to 40 digits",
    },
    {
        "theory_object": "Spectral gap Delta = lambda_1 - lambda_2",
        "physical_analog": "Mass gap",
        "status": "DERIVABLE",
        "numerical_value": "0.131",
        "evidence": "lambda_1 - lambda_2 from Galerkin",
    },
    {
        "theory_object": "Correlation length xi_2 = -1/ln(lambda_2/lambda_1)",
        "physical_analog": "Compton wavelength",
        "status": "DERIVABLE",
        "numerical_value": "0.716",
        "evidence": "From spectral gap, standard transfer matrix theory",
    },
    {
        "theory_object": "PDE: psi_{uv} = -mu * psi",
        "physical_analog": "Klein-Gordon equation",
        "status": "DERIVABLE",
        "numerical_value": "mu = 5.73",
        "evidence": "Exact PDE from continuum kernel",
    },
    {
        "theory_object": "S_BD_ren >= 0",
        "physical_analog": "Positive energy theorem",
        "status": "DERIVABLE",
        "numerical_value": "Proved in Lean",
        "evidence": "RenormalizedAction.lean (0 sorry)",
    },
    {
        "theory_object": "ADM decomposition: S = spatial + extrinsic",
        "physical_analog": "3+1 split of Einstein-Hilbert",
        "status": "DERIVABLE",
        "numerical_value": "Proved in Lean",
        "evidence": "ADMStructure.lean (0 sorry)",
    },
    {
        "theory_object": "S_d gauge symmetry",
        "physical_analog": "Coordinate reparametrization invariance",
        "status": "DERIVABLE",
        "numerical_value": "d! symmetry group",
        "evidence": "Product order permutation, SortedProfileFormula.lean",
    },
    {
        "theory_object": "Lorentzian overlap is linear in w",
        "physical_analog": "Massless graviton (no mass term in Hessian)",
        "status": "DERIVABLE",
        "numerical_value": "Proved in Lean",
        "evidence": "LorentzianBD.lean (0 sorry): d^2(overlap)/dw^2 = 0",
    },
    {
        "theory_object": "Universal local kernel K_comb",
        "physical_analog": "Dimension-independent local dynamics",
        "status": "DERIVABLE",
        "numerical_value": "Exact formula",
        "evidence": "DimensionalSpectralTheory.lean (0 sorry)",
    },
    {
        "theory_object": "Recursive dimensional law: gamma_{d+1} = (1/m) Sum f*gamma_slice",
        "physical_analog": "Dimensional reduction / holographic structure",
        "status": "DERIVABLE",
        "numerical_value": "Proved in Lean",
        "evidence": "RecursiveDimensionalLaw.lean + Factorization3D.lean (0 sorry)",
    },
    {
        "theory_object": "Kernel Lipschitz stability",
        "physical_analog": "UV regularity",
        "status": "DERIVABLE",
        "numerical_value": "|Delta count| <= 1",
        "evidence": "Robustness3D.lean (0 sorry)",
    },
    {
        "theory_object": "Gap bounds: 0 < gamma(m) <= 1",
        "physical_analog": "Bounded spectral density",
        "status": "DERIVABLE",
        "numerical_value": "Proved in Lean",
        "evidence": "GapBounds3D.lean (0 sorry)",
    },
    {
        "theory_object": "Continuum bridge: S_BD_ren = TV/2",
        "physical_analog": "Total variation = action functional",
        "status": "DERIVABLE",
        "numerical_value": "Exact identity",
        "evidence": "ContinuumBridge.lean (0 sorry)",
    },
    {
        "theory_object": "EH <= 4*BD and BD <= C*EH (mutual bounds)",
        "physical_analog": "BD and Einstein-Hilbert are spectrally equivalent",
        "status": "DERIVABLE",
        "numerical_value": "Proved in Lean",
        "evidence": "SpectralBDvsEH.lean (0 sorry)",
    },

    # --- STRUCTURAL: correct structure, needs interpretation ---
    {
        "theory_object": "Bessel mode p=1",
        "physical_analog": "Scalar field",
        "status": "STRUCTURAL",
        "numerical_value": "C_1 from Bessel fit",
        "evidence": "Mode expansion of eigenfunction, bessel_mode_system.py",
    },
    {
        "theory_object": "Width field w(p)",
        "physical_analog": "Metric degrees of freedom",
        "status": "STRUCTURAL",
        "numerical_value": "Profile analysis",
        "evidence": "(w, a) reduction captures 99%+ of variance",
    },
    {
        "theory_object": "Center field a(p)",
        "physical_analog": "Matter degrees of freedom",
        "status": "STRUCTURAL",
        "numerical_value": "91% decoupled from w",
        "evidence": "KL divergence test, fiber_decomposition.py",
    },
    {
        "theory_object": "beta(P) -> 0 geometrically",
        "physical_analog": "UV completeness / asymptotic safety",
        "status": "STRUCTURAL",
        "numerical_value": "r ~ 0.3-0.5",
        "evidence": "renormalization_flow.py, Galerkin convergence",
    },
    {
        "theory_object": "Confined surface: xi/m -> f(beta)",
        "physical_analog": "Confinement (no deconfining transition)",
        "status": "STRUCTURAL",
        "numerical_value": "c=2 + gapped correlations",
        "evidence": "Constrained surface theory, exact solution",
    },

    # --- SPECULATIVE: requires extrapolation ---
    {
        "theory_object": "Mode p > 1",
        "physical_analog": "Particle spectrum (higher excitations)",
        "status": "SPECULATIVE",
        "numerical_value": "E_p computed numerically",
        "evidence": "Mode hierarchy from Galerkin, hamiltonian_spectrum.py",
    },
    {
        "theory_object": "d = 4 preferred",
        "physical_analog": "Physical spacetime dimension",
        "status": "SPECULATIVE",
        "numerical_value": "gamma_4 predicted from recursive law",
        "evidence": "RecursiveDimensionalLaw.lean structure, numerical gamma_d",
    },
    {
        "theory_object": "xi_2 = l_Planck",
        "physical_analog": "Planck scale identification",
        "status": "SPECULATIVE",
        "numerical_value": "Factor ~1.5 tension",
        "evidence": "PlanckSpacing.lean (structure only, physics input needed)",
    },
    {
        "theory_object": "Euclidean -> Lorentzian rotation",
        "physical_analog": "Wick rotation",
        "status": "SPECULATIVE",
        "numerical_value": "Requires OS axioms",
        "evidence": "Not proved; standard in lattice QFT but non-trivial here",
    },
]


# ============================================================
# Print the dictionary
# ============================================================

def print_table():
    """Print the dictionary as a formatted table."""
    header = f"{'Theory Object':<52s} | {'Physical Analog':<38s} | {'Status':<11s} | {'Value':<22s} | {'Evidence'}"
    sep = "-" * len(header)

    print()
    print("=" * 100)
    print("COMPLETE THEORY-TO-PHYSICS DICTIONARY")
    print("Causal Algebraic Geometry -> Gravitational / Field-Theoretic Physics")
    print("=" * 100)
    print()
    print(header)
    print(sep)

    current_status = None
    for entry in dictionary:
        if entry["status"] != current_status:
            if current_status is not None:
                print(sep)
            current_status = entry["status"]
        print(f"{entry['theory_object']:<52s} | "
              f"{entry['physical_analog']:<38s} | "
              f"{entry['status']:<11s} | "
              f"{entry['numerical_value']:<22s} | "
              f"{entry['evidence']}")

    print(sep)
    print()


def print_lean_status():
    """Print what is proved in Lean."""
    print("=" * 100)
    print("LEAN FORMALIZATION STATUS")
    print("=" * 100)
    print()

    lean_files = [
        ("UniversalConcavityGeneral.lean", "Universal discrete concavity (all d >= 2)"),
        ("SortedProfileFormula.lean",      "Sorted profile decomposition"),
        ("EqualWidthOptimal.lean",         "Equal widths minimize S_BD at fixed content"),
        ("ADMStructure.lean",              "ADM decomposition + dominance + rigidity"),
        ("RenormalizedAction.lean",        "Positive energy: S_BD_ren >= 0, = 0 iff flat"),
        ("ContinuumBridge.lean",           "2D continuum bridge: S_BD_ren = TV/2"),
        ("ContinuumLimitReal.lean",        "FTC: |Delta w| <= integral |w'|"),
        ("SeparatedBumps.lean",            "Additivity of isolated defects"),
        ("WeakFieldLimit.lean",            "Weak-field identity: w*spatial = -Sum delta_i^2"),
        ("SpectralRelation.lean",          "F_BD = <u,u> and F_EH = <u,-Delta u>"),
        ("SpectralBDvsEH.lean",            "Mutual bounds: EH <= 4BD, BD <= CEH"),
        ("LorentzianBD.lean",              "Lorentzian overlap is linear (massless graviton)"),
        ("LorentzianHessian.lean",         "Hessian structure, saddle at flat"),
        ("DimensionalSpectralTheory.lean",  "Universal local kernel (all d)"),
        ("RecursiveDimensionalLaw.lean",    "Recursive dimensional spectral law"),
        ("Factorization3D.lean",           "gamma_3 = f_bulk * gamma_slice factorization"),
        ("Robustness3D.lean",              "Kernel Lipschitz stability"),
        ("GapBounds3D.lean",               "Rigorous bounds on spectral gap"),
    ]

    print("PROVED IN LEAN (18 core files, 0 sorry):")
    print()
    for filename, description in lean_files:
        print(f"  {filename:<42s}  {description}")

    print()


def print_numerical_status():
    """Print what is computed numerically."""
    print("=" * 100)
    print("NUMERICAL COMPUTATIONS")
    print("=" * 100)
    print()

    print("COMPUTED TO HIGH PRECISION:")
    print()
    print("  gamma_2 = 0.2764137...            (40 digits, certified_gap.py)")
    print("  lambda_comp = 0.34916...           (Galerkin, converged P=13)")
    print("  mu = 5.73...                       (PDE eigenvalue)")
    print("  xi_2 = 0.716...                    (correlation length)")
    print()

    print("COMPUTED TO MODERATE PRECISION:")
    print()
    print("  gamma_3 ~ 0.19                     (3D gap, gap_d3_fast.py)")
    print("  Bessel modes E_1, E_2, E_3         (hamiltonian_spectrum.py)")
    print("  RG flow beta(P) for P=1..12        (renormalization_flow.py)")
    print("  Contact probabilities P_d(r)       (contact_4d.py)")
    print()


def print_honest_gaps():
    """Print what is NOT derivable."""
    print("=" * 100)
    print("HONEST ASSESSMENT: WHAT IS NOT DERIVABLE")
    print("=" * 100)
    print()

    print("THE MODEL DOES NOT PREDICT (without additional physics input):")
    print()
    print("  1. PARTICLE MASSES: The model has a spectral gap and mode hierarchy,")
    print("     but the identification of modes with specific particles (electron,")
    print("     muon, W boson, etc.) requires additional structure not present")
    print("     in the constrained surface model.")
    print()
    print("  2. COUPLING CONSTANTS: The fine structure constant alpha = 1/137,")
    print("     the strong coupling g_s, and the weak mixing angle are not")
    print("     determined by the geometry alone.")
    print()
    print("  3. COSMOLOGICAL PARAMETERS: The cosmological constant Lambda,")
    print("     the dark energy equation of state, and inflation parameters")
    print("     are outside the scope of this lattice model.")
    print()
    print("  4. THE STANDARD MODEL GAUGE GROUP: SU(3) x SU(2) x U(1) does not")
    print("     emerge from the antitone constraint alone. The permutation")
    print("     symmetry S_d is a coordinate symmetry, not a gauge symmetry.")
    print()
    print("  5. FERMIONS: The model describes bosonic (symmetric) fields.")
    print("     Fermionic statistics require additional structure (e.g.,")
    print("     Grassmann variables, spin structure on the causal set).")
    print()

    print("THE GAP BETWEEN THE MODEL AND REAL PHYSICS:")
    print()
    print("  The constrained surface model is a STATISTICAL MECHANICS model")
    print("  on a causal lattice. It captures the THERMODYNAMIC sector of")
    print("  gravity (entropy, positive energy, variational principles).")
    print()
    print("  To make contact with real physics, one needs:")
    print()
    print("  (a) LATTICE SPACING = PLANCK LENGTH: an identification, not a derivation.")
    print("      The model predicts a correlation length xi; equating xi = l_Planck")
    print("      is a PHYSICS INPUT, not a mathematical theorem.")
    print()
    print("  (b) WICK ROTATION: the Euclidean theory must be analytically continued")
    print("      to Lorentzian signature. This requires Osterwalder-Schrader axioms,")
    print("      which are not verified for the constrained surface model.")
    print()
    print("  (c) DYNAMICS: the transfer matrix gives equilibrium correlations.")
    print("      Recovering the Einstein equations as equations of MOTION requires")
    print("      either Poisson sprinklings (Benincasa-Dowker 2010) or a separate")
    print("      dynamical principle.")
    print()
    print("  (d) MATTER COUPLING: the width/center decomposition is suggestive")
    print("      of gravity/matter separation, but the identification is structural,")
    print("      not derived from first principles.")
    print()

    print("SUMMARY OF STATUS COUNTS:")
    print()
    counts = {"DERIVABLE": 0, "STRUCTURAL": 0, "SPECULATIVE": 0}
    for entry in dictionary:
        counts[entry["status"]] += 1
    for status, count in counts.items():
        print(f"  {status:<12s}: {count:2d} entries")
    print(f"  {'TOTAL':<12s}: {sum(counts.values()):2d} entries")
    print()


# ============================================================
# Main
# ============================================================
if __name__ == "__main__":
    print_table()
    print_lean_status()
    print_numerical_status()
    print_honest_gaps()
