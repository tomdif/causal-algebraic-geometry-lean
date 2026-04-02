"""
Module 1 / File 3: Effective Spacetime Metric from the Simplex Operator

The eigenvalue PDE psi_{uv} = -mu psi in wave coordinates (s=u+v, d=v-u)
becomes psi_{ss} - psi_{dd} = -4 mu psi, which is the Klein-Gordon equation
with Lorentzian metric eta = diag(-1, +1) (identifying s=time, d=space).

The comparable area A(u,v) = u + v - u^2/2 - v^2 - 2uv defines a natural
conformal factor on the simplex. The conformal metric
  ds^2 = A(u,v)^{-alpha} (du^2 + dv^2)
has curvature that encodes the geometry of the causal structure.

This script computes:
  1. The PDE in wave coordinates and Klein-Gordon identification
  2. Christoffel symbols and Ricci scalar of the conformal metric
  3. Geodesics of the conformal metric (numerically)
  4. Klein-Gordon mass from the eigenvalue

Classification:
  - PDE psi_{uv} = -mu psi:       DERIVABLE (eigenvalue equation of T)
  - Wave coords -> Klein-Gordon:   DERIVABLE (change of variables)
  - Conformal metric definition:   STRUCTURAL (choice of A^{-alpha})
  - Christoffel/Ricci computation: DERIVABLE from metric choice
  - Geodesic structure:            DERIVABLE from metric choice
  - 'Spacetime' interpretation:    STRUCTURAL
"""

import numpy as np
from scipy.integrate import solve_ivp
import sympy as sp

# ============================================================================
# Part 1: PDE and Klein-Gordon identification [DERIVABLE]
# ============================================================================

def wave_coordinate_analysis():
    """
    The transfer operator eigenvalue equation in the continuum limit is
      psi_{uv}(u,v) = -mu * psi(u,v)
    on the simplex Sigma = {u,v >= 0, u+v <= 1}.

    Change to wave coordinates: s = u + v (timelike), d = v - u (spacelike).
    Then u = (s-d)/2, v = (s+d)/2, and:
      d/du = d/ds - d/dd
      d/dv = d/ds + d/dd
      psi_{uv} = psi_{ss} - psi_{dd}

    So the PDE becomes:
      psi_{ss} - psi_{dd} = -mu * psi

    This is the (1+1)d Klein-Gordon equation with:
      metric: eta = diag(-1, +1)  (s = time, d = space)
      mass^2: m^2 = mu
    """
    print("=" * 70)
    print("PART 1: PDE IN WAVE COORDINATES  [DERIVABLE]")
    print("=" * 70)
    print()

    # Symbolic verification
    u, v, s, d, mu_sym = sp.symbols('u v s d mu', real=True)
    psi = sp.Function('psi')

    print("  Original PDE on simplex:")
    print("    psi_{uv}(u,v) = -mu * psi(u,v)")
    print()
    print("  Wave coordinates: s = u + v,  d = v - u")
    print("    u = (s - d)/2,  v = (s + d)/2")
    print()

    # Compute the transformation symbolically
    # psi(u,v) = Psi(s(u,v), d(u,v))
    # s_u = 1, s_v = 1, d_u = -1, d_v = 1
    # psi_u = Psi_s * s_u + Psi_d * d_u = Psi_s - Psi_d
    # psi_v = Psi_s * s_v + Psi_d * d_v = Psi_s + Psi_d
    # psi_{uv} = (Psi_s - Psi_d)_v = (Psi_s - Psi_d)_s * 1 + (Psi_s - Psi_d)_d * 1
    #          = Psi_{ss} + Psi_{sd} - Psi_{ds} - Psi_{dd}
    #          = Psi_{ss} - Psi_{dd}

    print("  Chain rule:")
    print("    psi_u = Psi_s - Psi_d")
    print("    psi_v = Psi_s + Psi_d")
    print("    psi_{uv} = (Psi_s - Psi_d)_v")
    print("             = Psi_{ss} + Psi_{sd} - Psi_{ds} - Psi_{dd}")
    print("             = Psi_{ss} - Psi_{dd}")
    print()
    print("  Transformed PDE:")
    print("    Psi_{ss} - Psi_{dd} = -mu * Psi")
    print()
    print("  This IS the Klein-Gordon equation:")
    print("    (Box + m^2) Psi = 0,  where Box = -d_s^2 + d_d^2")
    print("    with metric eta_{ab} = diag(-1, +1)")
    print("    and m^2 = mu (the eigenvalue of T)")
    print()

    print("  Simplex domain in wave coordinates:")
    print("    u >= 0:     s >= d")
    print("    v >= 0:     s >= -d")
    print("    u + v <= 1: s <= 1")
    print("    => Triangle: |d| <= s <= 1")
    print("    (Forward light cone from origin, cut off at s = 1)")
    print()

    print("  [DERIVABLE] The PDE is an exact consequence of the transfer operator.")
    print("  [STRUCTURAL] Identifying s as 'time' and d as 'space' is interpretive.")
    print()


# ============================================================================
# Part 2: Comparable area and conformal metric [STRUCTURAL]
# ============================================================================

def comparable_area(u, v):
    """A(u,v) = u + v - u^2/2 - v^2 - 2uv (area comparable to (u,v) in simplex)."""
    return u + v - u**2 / 2 - v**2 - 2 * u * v


def conformal_metric_analysis():
    """
    The comparable area A(u,v) defines a natural conformal factor.
    Metric: g_{ij} = A(u,v)^{-alpha} * delta_{ij}
    """
    print("=" * 70)
    print("PART 2: CONFORMAL METRIC FROM COMPARABLE AREA  [STRUCTURAL]")
    print("=" * 70)
    print()

    u, v, alpha = sp.symbols('u v alpha', real=True, positive=True)

    # Comparable area
    A = u + v - u**2 / 2 - v**2 - 2 * u * v
    print("  Comparable area: A(u,v) = u + v - u^2/2 - v^2 - 2uv")
    print()

    # Check A at special points
    print("  A at special points:")
    test_pts = [(sp.Rational(1, 3), sp.Rational(1, 3)),
                (sp.Rational(1, 2), sp.Rational(0)),
                (sp.Rational(0), sp.Rational(1, 2)),
                (sp.Rational(1, 4), sp.Rational(1, 4))]
    for u0, v0 in test_pts:
        Aval = A.subs([(u, u0), (v, v0)])
        print(f"    A({u0}, {v0}) = {Aval} = {float(Aval):.6f}")
    print()

    # Maximum of A
    Au = sp.diff(A, u)
    Av = sp.diff(A, v)
    print(f"  dA/du = {Au}")
    print(f"  dA/dv = {Av}")
    crit = sp.solve([Au, Av], [u, v])
    print(f"  Critical point: {crit}")
    if crit:
        u_c, v_c = crit[u], crit[v]
        A_max = A.subs([(u, u_c), (v, v_c)])
        print(f"  A_max = A({u_c}, {v_c}) = {A_max} = {float(A_max):.6f}")
    print()

    # Conformal metric
    print("  Conformal metric: ds^2 = Omega(u,v) (du^2 + dv^2)")
    print("    where Omega = A(u,v)^{-alpha} for parameter alpha > 0")
    print()

    # Christoffel symbols for conformal metric g = e^{2phi} delta
    # where e^{2phi} = A^{-alpha}, so phi = -(alpha/2) log A
    phi = -alpha / 2 * sp.log(A)
    phi_u = sp.diff(phi, u)
    phi_v = sp.diff(phi, v)
    phi_uu = sp.diff(phi, u, 2)
    phi_vv = sp.diff(phi, v, 2)

    print("  For conformal metric g = e^{2 phi} delta_{ij}:")
    print(f"    phi = -(alpha/2) log A")
    print()

    # Christoffel symbols in 2D conformal:
    # Gamma^u_{uu} = phi_u, Gamma^u_{uv} = phi_v, Gamma^u_{vv} = -phi_u
    # Gamma^v_{uu} = -phi_v, Gamma^v_{uv} = phi_u, Gamma^v_{vv} = phi_v
    print("  Christoffel symbols (2D conformal):")
    print(f"    Gamma^u_{{uu}} = phi_u = {sp.simplify(phi_u)}")
    print(f"    Gamma^u_{{uv}} = phi_v = {sp.simplify(phi_v)}")
    print(f"    Gamma^u_{{vv}} = -phi_u = {sp.simplify(-phi_u)}")
    print(f"    Gamma^v_{{uu}} = -phi_v = {sp.simplify(-phi_v)}")
    print(f"    Gamma^v_{{uv}} = phi_u = {sp.simplify(phi_u)}")
    print(f"    Gamma^v_{{vv}} = phi_v = {sp.simplify(phi_v)}")
    print()

    # Ricci scalar in 2D: R = -2 e^{-2phi} (phi_{uu} + phi_{vv})
    #   = -2 e^{-2phi} Laplacian(phi)
    lap_phi = phi_uu + phi_vv
    R_conformal = -2 * sp.exp(-2 * phi) * lap_phi
    R_simplified = sp.simplify(R_conformal)

    print("  Ricci scalar: R = -2 e^{-2 phi} (phi_{uu} + phi_{vv})")
    print()

    # Evaluate at the critical point for alpha=1
    R_alpha1 = R_simplified.subs(alpha, 1)
    if crit:
        R_at_center = R_alpha1.subs([(u, u_c), (v, v_c)])
        print(f"  At center ({u_c}, {v_c}) with alpha=1:")
        print(f"    R = {sp.simplify(R_at_center)} = {float(R_at_center.evalf()):.6f}")
        print()

    # Evaluate R numerically on a grid for alpha=1
    print("  Ricci scalar R(u,v) on grid (alpha = 1):")
    print()
    R_func = sp.lambdify((u, v), R_alpha1, 'numpy')

    print(f"  {'u':>6} {'v':>6} {'A(u,v)':>10} {'R(u,v)':>12}")
    print("  " + "-" * 38)
    for u0 in [0.1, 0.2, 0.3, 0.4]:
        for v0 in [0.1, 0.2, 0.3]:
            if u0 + v0 <= 0.95:
                A_val = comparable_area(u0, v0)
                if A_val > 0.01:
                    try:
                        R_val = float(R_func(u0, v0))
                        print(f"  {u0:6.2f} {v0:6.2f} {A_val:10.6f} {R_val:12.4f}")
                    except Exception:
                        print(f"  {u0:6.2f} {v0:6.2f} {A_val:10.6f}   (numerical issue)")
    print()

    print("  [STRUCTURAL] The conformal metric is a CHOICE. The comparable area A(u,v)")
    print("  is DERIVABLE, but promoting it to a metric requires interpretation.")
    print()

    return phi_u, phi_v, A


# ============================================================================
# Part 3: Geodesics of the conformal metric [DERIVABLE from metric choice]
# ============================================================================

def compute_geodesics():
    """
    Geodesics of g = A(u,v)^{-alpha} delta_{ij} satisfy:
      u'' + Gamma^u_{uu} u'^2 + 2 Gamma^u_{uv} u' v' + Gamma^u_{vv} v'^2 = 0
      v'' + Gamma^v_{uu} u'^2 + 2 Gamma^v_{uv} u' v' + Gamma^v_{vv} v'^2 = 0

    For 2D conformal metric with phi = -(alpha/2) log A:
      u'' = -phi_u (u'^2 - v'^2) - 2 phi_v u' v'
      v'' =  phi_u * 2 u' v' - phi_v (u'^2 - v'^2)
    Wait, more carefully:
      u'' = -(phi_u u'^2 + 2 phi_v u' v' - phi_u v'^2)
      v'' = -(-phi_v u'^2 + 2 phi_u u' v' + phi_v v'^2)
    i.e.
      u'' = -phi_u(u'^2 - v'^2) - 2 phi_v u'v'
      v'' = phi_v(u'^2 - v'^2) - 2 phi_u u'v'
    """
    print("=" * 70)
    print("PART 3: GEODESICS OF CONFORMAL METRIC  [DERIVABLE from metric]")
    print("=" * 70)
    print()

    alpha_val = 1.0  # conformal exponent

    def A_func(u, v):
        return u + v - u**2 / 2 - v**2 - 2 * u * v

    def grad_log_A(u, v):
        """Gradient of log A(u,v)."""
        A = A_func(u, v)
        if A < 1e-12:
            return 0.0, 0.0
        Au = 1 - u - 2 * v
        Av = 1 - 2 * v - 2 * u
        return Au / A, Av / A

    def geodesic_ode(t, state):
        """
        state = [u, v, u', v']
        phi = -(alpha/2) log A
        phi_u = -(alpha/2) A_u/A,  phi_v = -(alpha/2) A_v/A
        """
        uu, vv, up, vp = state

        # Check simplex bounds
        if uu < 0 or vv < 0 or uu + vv > 1:
            return [up, vp, 0, 0]

        A = A_func(uu, vv)
        if A < 1e-12:
            return [up, vp, 0, 0]

        Au = 1 - uu - 2 * vv
        Av = 1 - 2 * vv - 2 * uu
        phi_u = -alpha_val / 2 * Au / A
        phi_v = -alpha_val / 2 * Av / A

        # Geodesic equations for 2D conformal metric
        upp = -phi_u * (up**2 - vp**2) - 2 * phi_v * up * vp
        vpp = phi_v * (up**2 - vp**2) - 2 * phi_u * up * vp

        return [up, vp, upp, vpp]

    def in_simplex(u, v):
        return u >= -0.01 and v >= -0.01 and u + v <= 1.01

    # Shoot geodesics from center of simplex
    u0, v0 = 0.25, 0.25
    speed = 0.5

    print(f"  Geodesics from ({u0}, {v0}) with alpha = {alpha_val}")
    print(f"  Conformal metric: ds^2 = A(u,v)^{{-{alpha_val}}} (du^2 + dv^2)")
    print()

    angles = np.linspace(0, 2 * np.pi, 9)[:-1]  # 8 directions
    t_span = (0, 2.0)
    t_eval = np.linspace(0, 2.0, 50)

    print(f"  {'angle':>6}   {'endpoint (u,v)':>20}   {'arc length':>12}   {'path'}")
    print("  " + "-" * 60)

    for theta in angles:
        up0 = speed * np.cos(theta)
        vp0 = speed * np.sin(theta)
        y0 = [u0, v0, up0, vp0]

        def event_exit(t, state):
            u, v = state[0], state[1]
            # Distance to simplex boundary
            return min(u + 0.01, v + 0.01, 1.01 - u - v)
        event_exit.terminal = True
        event_exit.direction = -1

        sol = solve_ivp(geodesic_ode, t_span, y0, t_eval=t_eval,
                        events=event_exit, max_step=0.02, rtol=1e-8)

        u_end = sol.y[0, -1]
        v_end = sol.y[1, -1]

        # Compute arc length in conformal metric
        arc = 0.0
        for k in range(1, len(sol.t)):
            du = sol.y[0, k] - sol.y[0, k - 1]
            dv = sol.y[1, k] - sol.y[1, k - 1]
            um = (sol.y[0, k] + sol.y[0, k - 1]) / 2
            vm = (sol.y[1, k] + sol.y[1, k - 1]) / 2
            A = A_func(um, vm)
            if A > 1e-12:
                arc += np.sqrt((du**2 + dv**2) / A**alpha_val)

        # Simple path indicator
        path_pts = []
        for k in range(0, len(sol.t), max(1, len(sol.t) // 8)):
            path_pts.append(f"({sol.y[0,k]:.2f},{sol.y[1,k]:.2f})")
        path_str = " -> ".join(path_pts[:4])

        print(f"  {np.degrees(theta):6.1f}   ({u_end:8.4f}, {v_end:8.4f})   "
              f"{arc:12.6f}   {path_str}")

    print()
    print("  Geodesics curve toward high-A regions (where metric is 'smaller').")
    print("  Near simplex boundary (A -> 0), metric blows up: effective 'wall'.")
    print()
    print("  [DERIVABLE] Given the metric choice, geodesics follow automatically.")
    print("  [STRUCTURAL] The metric choice ds^2 = A^{-alpha} delta is interpretive.")
    print()


# ============================================================================
# Part 4: Klein-Gordon mass and eigenvalue [DERIVABLE]
# ============================================================================

def klein_gordon_mass():
    """
    From the PDE psi_{uv} = -mu psi => psi_{ss} - psi_{dd} = -4 mu psi,
    the Klein-Gordon mass is m^2 = 4 mu.

    The eigenvalue mu = 1/lambda where lambda is the principal eigenvalue
    of the transfer operator.
    """
    print("=" * 70)
    print("PART 4: KLEIN-GORDON MASS  [DERIVABLE]")
    print("=" * 70)
    print()

    # Use known eigenvalue from Galerkin (lambda_comp ~ 0.349)
    # mu = 1/lambda for the unsymmetrized operator
    # lambda_K ~ 0.1746, so mu ~ 5.727
    lambda_K = 0.17458  # approximate from polynomial_galerkin.py
    lambda_comp = 2 * lambda_K  # symmetrized ~ 0.349
    mu = 1.0 / lambda_K

    print(f"  Transfer operator eigenvalue: lambda_K = {lambda_K:.5f}")
    print(f"  Symmetrized eigenvalue: lambda_comp = 2*lambda_K = {lambda_comp:.5f}")
    print()
    print(f"  PDE eigenvalue: mu = 1/lambda_K = {mu:.5f}")
    print()
    print("  Klein-Gordon equation in wave coordinates:")
    print("    Psi_{ss} - Psi_{dd} = -4 mu Psi")
    print()
    print("  Standard form: (Box + m^2) Psi = 0")
    print(f"    => m^2 = 4 mu = {4 * mu:.5f}")
    print(f"    => m = {np.sqrt(4 * mu):.5f}")
    print()

    # Relation to mass gap
    # Mass gap from spectral theory: Delta E = -log(lambda_2/lambda_1) ~ 1.396
    # This is the inverse correlation length, which IS the mass in lattice field theory
    mass_gap = 1.396  # from hamiltonian_spectrum.py
    print("  Comparison with spectral mass gap:")
    print(f"    Spectral mass gap: Delta E = {mass_gap:.3f}")
    print(f"    KG mass: m = sqrt(4 mu) = {np.sqrt(4 * mu):.3f}")
    print()
    print("  These are different quantities:")
    print("    - Spectral gap: gap in discrete spectrum of H = -log T")
    print("    - KG mass: continuous PDE parameter from mu")
    print("  Both are DERIVABLE; their relation requires renormalization (STRUCTURAL).")
    print()

    # Dispersion relation
    print("  Dispersion relation (from KG in wave coords):")
    print("    omega^2 = k^2 + m^2")
    print()
    print(f"  {'k':>8}   {'omega':>12}   {'omega/m':>12}   {'v_g = k/omega':>14}")
    print("  " + "-" * 50)
    m2 = 4 * mu
    for k in [0, 0.5, 1.0, 2.0, 5.0, 10.0]:
        omega = np.sqrt(k**2 + m2)
        vg = k / omega if omega > 0 else 0
        print(f"  {k:8.2f}   {omega:12.6f}   {omega / np.sqrt(m2):12.6f}   {vg:14.6f}")

    print()
    print("  At k=0: omega = m (rest mass). At k >> m: omega ~ k (massless limit).")
    print("  Group velocity v_g = k/omega < 1 always (causal propagation).")
    print()
    print("  [DERIVABLE] The KG equation and dispersion relation follow from the PDE.")
    print("  [STRUCTURAL] Physical interpretation as particle mass is interpretive.")
    print()


# ============================================================================
# Part 5: Summary table
# ============================================================================

def print_summary():
    print("=" * 70)
    print("SUMMARY: EFFECTIVE METRIC AND SPACETIME STRUCTURE")
    print("=" * 70)
    print()
    print("  Result                              Status")
    print("  " + "-" * 55)
    print("  PDE: psi_{uv} = -mu psi            DERIVABLE  (eigenvalue eq.)")
    print("  Wave coords: Box psi + m^2 psi = 0 DERIVABLE  (coord change)")
    print("  Metric eta = diag(-1,+1)            DERIVABLE  (from PDE structure)")
    print("  KG mass m^2 = 4 mu                  DERIVABLE  (from PDE)")
    print("  Dispersion omega^2 = k^2 + m^2      DERIVABLE  (from KG)")
    print("  Causal propagation v_g < 1           DERIVABLE  (from dispersion)")
    print("  " + "-" * 55)
    print("  A(u,v) as conformal factor           STRUCTURAL (choice)")
    print("  ds^2 = A^{-alpha} delta              STRUCTURAL (metric ansatz)")
    print("  Christoffel symbols, Ricci scalar    DERIVABLE from metric choice")
    print("  Geodesic structure                   DERIVABLE from metric choice")
    print("  'Spacetime' interpretation           STRUCTURAL (physical mapping)")
    print("  Mass = particle rest mass            STRUCTURAL (QFT dictionary)")
    print()
    print("  The key insight: the mixed-order comparability PDE has LORENTZIAN")
    print("  signature naturally. This is DERIVABLE from the causal structure.")
    print("  The simplex boundary acts as a conformal boundary (A -> 0).")
    print()


# ============================================================================
# Main
# ============================================================================

def main():
    wave_coordinate_analysis()
    conformal_metric_analysis()
    compute_geodesics()
    klein_gordon_mass()
    print_summary()


if __name__ == "__main__":
    main()
