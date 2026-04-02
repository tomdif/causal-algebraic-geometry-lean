"""
Action functional S[u,v] for the d=2 constrained surface field theory.

The d=2 model lives on the simplex Sigma = {(u,v) : u,v >= 0, u+v <= 1}.
Transfer operator: (Kf)(u,v) = int_0^u int_v^{1-u'} f(u',v') dv' du'

The symmetrized kernel K_s(P,Q) = (1/2) * 1_{P,Q comparable in mixed order}
where comparable means u' <= u and v' >= v, or u' >= u and v' <= v.

For a path P_0, ..., P_L through the simplex:
  W[path] = prod_{i} K_s(P_i, P_{i+1})
  S[path] = -log W = -sum log K_s(P_i, P_{i+1})

In the continuum limit this becomes S[path] = int L(u,v,u',v') dt.

This script:
  1. Computes the comparable area A(u,v) at each simplex point
  2. Derives the Lagrangian L(u,v) = -log A(u,v)
  3. Finds the saddle point and Euler-Lagrange equations
  4. Compares with the eigenvalue gamma_2 ~ 0.276
"""

import numpy as np
from scipy import integrate, optimize
import sympy as sp

# ===========================================================================
# Part 1: Comparable area computation
# ===========================================================================

def comparable_area_numeric(u, v):
    """
    Compute the area of the region comparable to (u,v) in mixed order.

    A point (u',v') in Sigma is comparable to (u,v) if either:
      (a) u' <= u and v' >= v  (with u'+v' <= 1, u' >= 0, v' >= 0)
      (b) u' >= u and v' <= v  (with u'+v' <= 1, u' >= 0, v' >= 0)

    Region (a): u' in [0,u], v' in [v, 1-u']
      Area_a = int_0^u (1-u'-v) du' = u - u^2/2 - u*v
             = u(1 - u/2 - v)

    Region (b): u' in [u, 1-v], v' in [0, min(v, 1-u')]
      For u' in [u, 1-v]: 1-u' >= v, so min(v, 1-u') = v
      Area_b = int_u^{1-v} v du' = v(1-v-u)

    But we must subtract the point (u,v) itself (measure zero, no effect).

    Total: A(u,v) = u(1 - u/2 - v) + v(1 - v - u)
                  = u - u^2/2 - uv + v - v^2 - uv
                  = u + v - u^2/2 - v^2 - 2uv
    """
    if u < 0 or v < 0 or u + v > 1 + 1e-12:
        return 0.0
    # Region (a): u' in [0,u], v' in [v, 1-u']
    # Need 1-u' >= v, i.e., u' <= 1-v. Since u' <= u and u+v <= 1, this holds.
    area_a = u * (1 - u / 2 - v)
    # Region (b): u' in [u, 1-v], v' in [0, v]
    # Need u <= 1-v, i.e., u+v <= 1. This holds by assumption.
    area_b = v * (1 - v - u)
    return max(area_a + area_b, 0.0)


def comparable_area_analytic(u, v):
    """Analytic formula: A(u,v) = u + v - u^2/2 - v^2 - 2uv."""
    return u + v - u**2 / 2 - v**2 - 2 * u * v


def verify_comparable_area():
    """Verify analytic formula against direct numerical integration."""
    print("=" * 70)
    print("PART 1: Comparable Area A(u,v)")
    print("=" * 70)
    print()
    print("Analytic formula: A(u,v) = u(1 - u/2 - v) + v(1 - v - u)")
    print("                        = u + v - u^2/2 - v^2 - 2uv")
    print()

    # Verify against numerical integration at sample points
    test_pts = [(0.2, 0.3), (0.1, 0.1), (0.4, 0.1), (0.3, 0.3),
                (0.0, 0.5), (0.5, 0.0), (1/3, 1/3)]
    print("Verification: analytic vs numerical integration")
    print(f"{'(u,v)':<16} {'Analytic':<14} {'Numerical':<14} {'Match':<6}")
    print("-" * 50)
    for u0, v0 in test_pts:
        if u0 + v0 > 1 + 1e-10:
            continue
        analytic = comparable_area_analytic(u0, v0)

        # Numerical: region (a)
        if u0 > 0 and v0 < 1:
            num_a, _ = integrate.dblquad(
                lambda vp, up: 1.0,
                0, u0,
                lambda up: v0,
                lambda up: 1 - up
            )
        else:
            num_a = 0.0

        # Numerical: region (b)
        if v0 > 0 and u0 < 1:
            num_b, _ = integrate.dblquad(
                lambda vp, up: 1.0,
                u0, 1 - v0,
                lambda up: 0,
                lambda up: v0
            )
        else:
            num_b = 0.0

        numerical = num_a + num_b
        match = abs(analytic - numerical) < 1e-8
        print(f"({u0:.2f}, {v0:.2f})   {analytic:12.8f}  {numerical:12.8f}  {'OK' if match else 'FAIL'}")

    print()


# ===========================================================================
# Part 2: Grid display of A(u,v) and L(u,v) = -log A(u,v)
# ===========================================================================

def display_grids():
    """Show A(u,v) and L(u,v) on a grid over the simplex."""
    print("=" * 70)
    print("PART 2: Comparable Area and Lagrangian on Simplex Grid")
    print("=" * 70)
    print()

    N = 10
    print(f"A(u,v) at grid points (N={N}):")
    header = "u\\v"
    print(f"{header:<6}", end="")
    for j in range(N + 1):
        v = j / N
        print(f"{v:7.2f}", end="")
    print()
    print("-" * (6 + 7 * (N + 1)))

    for i in range(N + 1):
        u = i / N
        print(f"{u:<6.2f}", end="")
        for j in range(N + 1):
            v = j / N
            if u + v > 1 + 1e-10:
                print(f"{'---':>7}", end="")
            else:
                a = comparable_area_analytic(u, v)
                print(f"{a:7.4f}", end="")
        print()

    print()
    print(f"L(u,v) = -log A(u,v) at grid points:")
    header = "u\\v"
    print(f"{header:<6}", end="")
    for j in range(N + 1):
        v = j / N
        print(f"{v:7.2f}", end="")
    print()
    print("-" * (6 + 7 * (N + 1)))

    for i in range(N + 1):
        u = i / N
        print(f"{u:<6.2f}", end="")
        for j in range(N + 1):
            v = j / N
            if u + v > 1 + 1e-10:
                print(f"{'---':>7}", end="")
            else:
                a = comparable_area_analytic(u, v)
                if a > 1e-15:
                    L = -np.log(a)
                    print(f"{L:7.3f}", end="")
                else:
                    print(f"{'inf':>7}", end="")
        print()
    print()


# ===========================================================================
# Part 3: Symbolic derivation of the Lagrangian and Euler-Lagrange
# ===========================================================================

def symbolic_derivation():
    """Derive the Euler-Lagrange equations symbolically."""
    print("=" * 70)
    print("PART 3: Symbolic Lagrangian and Euler-Lagrange Equations")
    print("=" * 70)
    print()

    u, v = sp.symbols('u v')

    # Comparable area
    A = u + v - u**2 / 2 - v**2 - 2 * u * v
    A_simplified = sp.simplify(A)
    print(f"Comparable area: A(u,v) = {A_simplified}")
    print(f"  = u(1 - u/2 - v) + v(1 - v - u)")
    print()

    # Factor and analyze
    A_factored = sp.factor(A)
    print(f"Factored: A = {A_factored}")
    print()

    # Lagrangian
    L = -sp.log(A)
    print(f"Lagrangian: L(u,v) = -log(A(u,v)) = -log({A_simplified})")
    print()

    # Partial derivatives (needed for Euler-Lagrange)
    dL_du = sp.diff(L, u)
    dL_dv = sp.diff(L, v)
    d2L_du2 = sp.diff(L, u, 2)
    d2L_dv2 = sp.diff(L, v, 2)
    d2L_dudv = sp.diff(L, u, v)

    dL_du_s = sp.simplify(dL_du)
    dL_dv_s = sp.simplify(dL_dv)

    print("Partial derivatives of L:")
    print(f"  dL/du = {dL_du_s}")
    print(f"  dL/dv = {dL_dv_s}")
    print()

    # Partial derivatives of A
    dA_du = sp.diff(A, u)
    dA_dv = sp.diff(A, v)
    print(f"Partial derivatives of A:")
    print(f"  dA/du = {sp.simplify(dA_du)} = 1 - u - 2v")
    print(f"  dA/dv = {sp.simplify(dA_dv)} = 1 - 2v - 2u")
    print()

    # -----------------------------------------------------------------------
    # The action functional for a path gamma(t) = (u(t), v(t)), t in [0,T]:
    #   S[gamma] = int_0^T L(u(t), v(t)) dt = -int_0^T log A(u(t), v(t)) dt
    #
    # But the full action also includes the path weight from the kernel,
    # which depends on the transition probabilities. For the smoothed kernel:
    #   K_smooth(P, Q) ~ A(midpoint) * exp(-distance^2 / 2*area)
    #
    # The simplest (zeroth order) action is just:
    #   S_0[gamma] = -int log A(u(t), v(t)) dt
    #
    # Euler-Lagrange: dL/du = 0 and dL/dv = 0 for a static saddle point.
    # For a dynamic path: d/dt (dL/du') - dL/du = 0 etc.
    # Since L_0 has no u' dependence, the static E-L is just:
    #   dA/du / A = 0  =>  dA/du = 0
    #   dA/dv / A = 0  =>  dA/dv = 0
    # -----------------------------------------------------------------------

    print("=" * 70)
    print("EULER-LAGRANGE for static saddle point (constant path)")
    print("=" * 70)
    print()
    print("For S_0[gamma] = -int log A(u,v) dt, the static saddle satisfies:")
    print("  dA/du = 0  and  dA/dv = 0")
    print()

    # Solve
    crit = sp.solve([dA_du, dA_dv], [u, v], dict=True)
    print(f"Critical point solutions: {crit}")
    print()

    if crit:
        u_star = crit[0][u]
        v_star = crit[0][v]
        A_star = A.subs([(u, u_star), (v, v_star)])
        L_star = L.subs([(u, u_star), (v, v_star)])
        print(f"  u* = {u_star} = {float(u_star):.10f}")
        print(f"  v* = {v_star} = {float(v_star):.10f}")
        print(f"  u* + v* = {sp.simplify(u_star + v_star)} = {float(u_star + v_star):.10f}")
        print(f"  A(u*,v*) = {sp.simplify(A_star)} = {float(A_star):.10f}")
        print(f"  L(u*,v*) = -log(A*) = {float(-sp.log(A_star)):.10f}")
        print()

        # Check: is the critical point inside the simplex?
        in_simplex = float(u_star) > 0 and float(v_star) > 0 and float(u_star + v_star) < 1
        print(f"  Inside simplex: {in_simplex}")
        print()

    # -----------------------------------------------------------------------
    # Full action with kinetic term
    # -----------------------------------------------------------------------
    print("=" * 70)
    print("FULL ACTION with kinetic term")
    print("=" * 70)
    print()
    print("For a path (u(t), v(t)) with small step (du, dv) = (u'dt, v'dt):")
    print("The transition kernel from (u,v) to (u+du, v+dv) has weight")
    print("proportional to the area of the overlap region.")
    print()
    print("To first order, the kernel is:")
    print("  K((u,v) -> (u+du, v+dv)) ~ A(u,v)  if (du,dv) stays comparable")
    print()
    print("The full continuum action is:")
    print("  S[u,v] = -int_0^T log A(u(t), v(t)) dt")
    print()
    print("This is a POTENTIAL-only action (no kinetic term in the transfer")
    print("operator formulation, since K_s depends only on comparability,")
    print("not on distance).")
    print()

    # -----------------------------------------------------------------------
    # Connection to the PDE: psi_{uv} = -mu * psi
    # -----------------------------------------------------------------------
    print("=" * 70)
    print("CONNECTION TO PDE: psi_uv = -mu * psi")
    print("=" * 70)
    print()
    print("The eigenvalue equation for the transfer operator K is:")
    print("  (K psi)(u,v) = gamma * psi(u,v)")
    print()
    print("Differentiating twice: psi_{uv}(u,v) = -gamma^{-1} * psi(u,v)")
    print("  (since d/du d/dv of the integral reproduces the integrand)")
    print()
    print("So mu = 1/gamma is the PDE eigenvalue.")
    print()

    # The WKB/semiclassical connection:
    # psi ~ exp(-phi/epsilon) => phi_u * phi_v = mu (eikonal equation)
    # The Lagrangian -log A plays the role of the phase phi.

    phi = -sp.log(A)
    phi_u = sp.diff(phi, u)
    phi_v = sp.diff(phi, v)
    product = sp.simplify(phi_u * phi_v)

    print("WKB ansatz: psi ~ exp(-S) where S = -log A(u,v)")
    print(f"  S_u = {sp.simplify(phi_u)}")
    print(f"  S_v = {sp.simplify(phi_v)}")
    print(f"  S_u * S_v = {product}")
    print()

    # Evaluate at critical point
    if crit:
        prod_at_crit = product.subs([(u, u_star), (v, v_star)])
        print(f"  S_u * S_v at (u*,v*) = {sp.simplify(prod_at_crit)} = {float(prod_at_crit):.10f}")
        print(f"  (This is 0 at the critical point, as expected: S_u = S_v = 0)")
        print()

    # Second-order WKB: psi ~ A^alpha for some power alpha
    # psi_{uv} = alpha * A^{alpha-2} * (A * A_{uv} + (alpha-1) * A_u * A_v)
    # = -mu * A^alpha
    # => alpha * (A_{uv}/A + (alpha-1)*A_u*A_v/A^2) = -mu

    alpha = sp.Symbol('alpha')
    A_uv = sp.diff(A, u, v)
    A_u = sp.diff(A, u)
    A_v = sp.diff(A, v)

    print(f"Power-law ansatz: psi = A(u,v)^alpha")
    print(f"  A_u  = {sp.simplify(A_u)}")
    print(f"  A_v  = {sp.simplify(A_v)}")
    print(f"  A_uv = {sp.simplify(A_uv)}")
    print()
    print(f"  psi_uv = alpha * A^(alpha-2) * [A * A_uv + (alpha-1) * A_u * A_v]")
    print(f"  -mu * psi = -mu * A^alpha")
    print()
    print(f"  => alpha * [A_uv + (alpha-1) * A_u * A_v / A] = -mu * A")
    print()
    print(f"  A_uv = {A_uv}")
    print(f"  This is constant = {A_uv}, so psi = A^alpha gives:")
    print(f"  alpha * [{A_uv} + (alpha-1) * A_u * A_v / A] = -mu * A")
    print()
    print(f"  This is NOT separable (A_u*A_v/A depends on (u,v)),")
    print(f"  so psi = A^alpha is NOT an exact eigenfunction.")
    print()

    return crit


# ===========================================================================
# Part 4: Discrete path weight computation
# ===========================================================================

def discrete_path_weights():
    """Compute path weights on a discretized simplex."""
    print("=" * 70)
    print("PART 4: Discrete Path Weights on Simplex")
    print("=" * 70)
    print()

    N = 20  # grid resolution
    # Grid points on the simplex
    pts = []
    for i in range(N + 1):
        for j in range(N + 1 - i):
            pts.append((i / N, j / N))
    print(f"Grid: N={N}, {len(pts)} points on simplex")
    print()

    # Comparability: (u1,v1) <= (u2,v2) iff u1 <= u2 and v1 >= v2
    def comparable(p, q):
        return (p[0] <= q[0] + 1e-12 and p[1] >= q[1] - 1e-12) or \
               (p[0] >= q[0] - 1e-12 and p[1] <= q[1] + 1e-12)

    # Count comparable pairs
    n_comparable = 0
    n_total = 0
    for i, p in enumerate(pts):
        for j, q in enumerate(pts):
            if i < j:
                n_total += 1
                if comparable(p, q):
                    n_comparable += 1

    print(f"Comparable pairs: {n_comparable} / {n_total} = {n_comparable/n_total:.4f}")
    print()

    # For the smoothed kernel, the weight K_s(P,Q) = A(midpoint)
    # or more precisely the volume of the comparable cone.
    # Compute the average -log A over the simplex
    total_logA = 0.0
    count = 0
    for u_i, v_i in pts:
        a = comparable_area_analytic(u_i, v_i)
        if a > 1e-15:
            total_logA += -np.log(a)
            count += 1

    print(f"Average Lagrangian <L> = <-log A> = {total_logA/count:.6f}")
    print()

    # The free energy per unit length is related to gamma_2
    # gamma_2 = leading eigenvalue ~ 0.276
    # -log(gamma_2) ~ 1.287
    print(f"Comparison with gamma_2:")
    gamma2 = 0.2763932  # known value
    print(f"  gamma_2 = {gamma2:.7f}")
    print(f"  -log(gamma_2) = {-np.log(gamma2):.7f}")
    print()


# ===========================================================================
# Part 5: Saddle point analysis and comparison with gamma_2
# ===========================================================================

def saddle_point_analysis():
    """Find the saddle point and compare with eigenvalue."""
    print("=" * 70)
    print("PART 5: Saddle Point Analysis")
    print("=" * 70)
    print()

    # The comparable area
    def A(u, v):
        return u + v - u**2 / 2 - v**2 - 2 * u * v

    def neg_A(x):
        u, v = x
        if u < 0 or v < 0 or u + v > 1:
            return 1e10
        return -A(u, v)

    # Find maximum of A (minimum of -log A = saddle of action)
    from scipy.optimize import minimize
    res = minimize(neg_A, [0.3, 0.2], method='Nelder-Mead')
    u_opt, v_opt = res.x
    A_opt = A(u_opt, v_opt)

    print(f"Maximum of A(u,v) on simplex:")
    print(f"  u* = {u_opt:.10f}")
    print(f"  v* = {v_opt:.10f}")
    print(f"  u* + v* = {u_opt + v_opt:.10f}")
    print(f"  A(u*,v*) = {A_opt:.10f}")
    print(f"  L(u*,v*) = -log A* = {-np.log(A_opt):.10f}")
    print()

    # Analytic: solve dA/du = 1-u-2v = 0, dA/dv = 1-2v-2u = 0
    # From first: u = 1-2v. Substitute into second: 1-2v-2(1-2v) = 1-2v-2+4v = -1+2v = 0
    # => v = 1/2, u = 1-1 = 0.  But (0, 1/2) is on the boundary!
    # Let's re-derive more carefully.
    print("Analytic critical point:")
    print("  dA/du = 1 - u - 2v = 0  =>  u = 1 - 2v")
    print("  dA/dv = 1 - 2v - 2u = 0  =>  2u = 1 - 2v = u  =>  u = 0")
    print("  => u* = 0, v* = 1/2")
    print("  This is on the BOUNDARY of the simplex (u=0 edge).")
    print()
    print(f"  A(0, 1/2) = {A(0, 0.5):.10f}")
    print(f"  L(0, 1/2) = {-np.log(A(0, 0.5)):.10f}")
    print()

    # By symmetry check: what about the u-axis?
    # dA/du|_{v=0} = 1-u, dA/dv|_{v=0} = 1-2u
    # Interior of u-axis: dA/du = 0 => u=1 (vertex), dA/dv = 0 => u=1/2
    print("Along v=0 edge: A(u,0) = u - u^2/2 = u(1-u/2)")
    print(f"  max at u=1: A(1,0) = {A(1,0):.4f} (vertex)")
    print(f"  A(1/2, 0) = {A(0.5, 0):.4f}")
    print()

    # The true maximum of A on the simplex
    # A(u,v) = u + v - u^2/2 - v^2 - 2uv
    # On the interior of the simplex, Hessian:
    #   A_uu = -1, A_vv = -2, A_uv = -2
    #   det(H) = (-1)(-2) - (-2)^2 = 2 - 4 = -2 < 0
    # So A has a SADDLE at the interior critical point (0, 1/2).
    # Wait -- critical point is on boundary. Let's check the Hessian at interior.
    print("Hessian of A:")
    print("  A_uu = -1,  A_vv = -2,  A_uv = -2")
    print("  det(H) = (-1)(-2) - (-2)^2 = 2 - 4 = -2 < 0")
    print("  => A has a SADDLE in (u,v) space (indefinite Hessian)")
    print("  => No interior maximum; max is on the boundary.")
    print()

    # Scan boundary edges for maximum of A
    # Edge 1: u=0, v in [0,1]: A(0,v) = v - v^2, max at v=1/2, A=1/4
    # Edge 2: v=0, u in [0,1]: A(u,0) = u - u^2/2, max at u=1, A=1/2
    # Edge 3: u+v=1, u in [0,1]: A(u,1-u) = u+(1-u)-u^2/2-(1-u)^2-2u(1-u)
    #   = 1 - u^2/2 - 1 + 2u - u^2 - 2u + 2u^2 = u^2/2
    #   max at u=1: A(1,0) = 1/2

    print("Boundary analysis:")
    print("  Edge u=0: A(0,v) = v(1-v),        max at v=1/2: A = 1/4")
    print("  Edge v=0: A(u,0) = u(1-u/2),      max at u=1:   A = 1/2")
    print("  Edge u+v=1: A(u,1-u) = u^2/2,     max at u=1:   A = 1/2")
    print()
    print("  Global max of A = 1/2 at vertices (1,0) and (0,1)... wait:")
    print(f"  A(1,0) = {A(1.0, 0.0):.4f}")
    print(f"  A(0,1) = {A(0.0, 1.0):.4f}")
    print(f"  A(0, 0.5) = {A(0.0, 0.5):.4f}")
    print(f"  A(0.5, 0) = {A(0.5, 0.0):.4f}")
    print()

    # The action functional at the saddle
    # For static (constant) paths: S = T * L(u,v) = -T * log A(u,v)
    # The partition function Z ~ exp(-S_min) ~ A_max^T
    # So gamma_2 ~ max_simplex A(u,v)? No -- gamma_2 is the operator eigenvalue.
    #
    # Actually the connection is:
    # Z_T = Tr(K^T) ~ gamma_2^T for large T
    # The saddle-point approximation of the path integral gives
    # gamma_2 ~ exp(-min_path S/T)
    # But for constant paths: S/T = -log A(u,v)
    # So gamma_2 <= max A(u,v) = 1/2

    print("Saddle-point estimate of gamma_2:")
    print(f"  max A = 1/2 at (1,0)")
    print(f"  This gives upper bound: gamma_2 <= 1/2")
    print(f"  Actual gamma_2 = 0.2764 < 1/2 (consistent)")
    print()

    # Better estimate: the eigenvalue comes from the full operator,
    # not just the diagonal part. The action for a non-constant path
    # includes the constraint that the path must be comparable at each step.
    # The effective action integrates over ALL comparable paths.

    # Integral of A over simplex = effective partition function per step
    A_integral, _ = integrate.dblquad(
        lambda v, u: A(u, v),
        0, 1,
        lambda u: 0,
        lambda u: 1 - u
    )
    simplex_area = 0.5
    A_avg = A_integral / simplex_area

    print(f"Average A over simplex:")
    print(f"  int A dA = {A_integral:.10f}")
    print(f"  <A> = int A / (area of simplex) = {A_avg:.10f}")
    print()

    # Symbolic computation of int A
    u_s, v_s = sp.symbols('u v', nonneg=True)
    A_sym = u_s + v_s - u_s**2 / 2 - v_s**2 - 2 * u_s * v_s
    integral_A = sp.integrate(
        sp.integrate(A_sym, (v_s, 0, 1 - u_s)),
        (u_s, 0, 1)
    )
    print(f"  Exact: int_Sigma A dA = {integral_A} = {float(integral_A):.10f}")
    print()

    # The eigenvalue gamma_2 satisfies: K psi = gamma_2 psi
    # (K 1)(u,v) = int_0^u int_v^{1-u'} du' dv' = integral of 1 over comparable region below
    # This is just region (a) above: area_a = u(1-u/2-v)
    K1_val = lambda u, v: u * (1 - u / 2 - v)

    print("K applied to constant function 1:")
    print("  (K 1)(u,v) = u(1 - u/2 - v)")
    print()
    print(f"  (K 1)(0.3, 0.2) = {K1_val(0.3, 0.2):.6f}")
    print(f"  (K 1)(0.5, 0.0) = {K1_val(0.5, 0.0):.6f}")
    print()

    # The Rayleigh quotient gives gamma_2 ~ <psi, K psi> / <psi, psi>
    # With trial psi = A^alpha, we can estimate gamma_2.
    # But the exact eigenfunction is known from the PDE.

    print("=" * 70)
    print("COMPARISON: Action functional vs eigenvalue gamma_2 = 0.2764")
    print("=" * 70)
    print()
    print("The action functional S[u,v] = -int log A(u(t),v(t)) dt describes")
    print("the 'cost' of a path through the simplex in the transfer operator")
    print("formulation.")
    print()
    print("Key results:")
    print(f"  1. A(u,v) = u + v - u^2/2 - v^2 - 2uv")
    print(f"  2. max A = 1/2 at (1,0), giving upper bound gamma_2 <= 1/2")
    print(f"  3. Hessian of A is indefinite (saddle), no interior max")
    print(f"  4. The eigenvalue gamma_2 = 0.2764 comes from the FULL")
    print(f"     spectral problem, not the static saddle point.")
    print()
    print("The Euler-Lagrange equation for S is:")
    print("  d/dt(dL/du') - dL/du = 0,  where L = -log A(u,v)")
    print("  For static paths: dA/du = 0, dA/dv = 0")
    print("  => 1-u-2v = 0 and 1-2v-2u = 0")
    print("  => u* = 0, v* = 1/2  (boundary point)")
    print()
    print("This connects to the PDE psi_{uv} = -mu*psi via the WKB ansatz:")
    print("  psi ~ exp(-S)  =>  S_u * S_v = mu  (eikonal equation)")
    print(f"  At (u*,v*) = (0, 1/2): S_u*S_v = 0 (degenerate)")
    print(f"  The full eigenvalue mu = 1/gamma_2 = {1/0.2764:.4f}")
    print()


# ===========================================================================
# Part 6: Transition density and refined action
# ===========================================================================

def transition_density():
    """Compute the transition density for the transfer operator."""
    print("=" * 70)
    print("PART 6: Transition Density and Refined Action")
    print("=" * 70)
    print()

    # The transfer operator K has kernel:
    #   K(u,v; u',v') = 1  if 0 <= u' <= u and v <= v' <= 1-u'
    #                 = 0  otherwise
    #
    # The transition density (normalized) from (u,v) is:
    #   rho(u',v' | u,v) = K(u,v; u',v') / (K 1)(u,v)
    #                    = 1 / [u(1 - u/2 - v)]  on the comparable region

    # For a path discretized at dt intervals:
    #   P(path) = prod_i K(P_i; P_{i+1}) / Z
    # Taking logs:
    #   S[path] = -sum_i log K(P_i; P_{i+1})
    #           = -sum_i log [u_i(1 - u_i/2 - v_i)]  (if transition is valid)
    #           = sum_i [-log(K 1)(u_i, v_i)]
    #           = sum_i L_K(u_i, v_i)
    #
    # where L_K(u,v) = -log[u(1-u/2-v)] is the "one-sided" Lagrangian.

    print("One-sided Lagrangian (from K, not K_s):")
    print("  L_K(u,v) = -log[u(1-u/2-v)]")
    print("  L_K = -log(u) - log(1-u/2-v)")
    print()

    u, v = sp.symbols('u v', positive=True)
    L_K = -sp.log(u * (1 - u / 2 - v))
    dLK_du = sp.simplify(sp.diff(L_K, u))
    dLK_dv = sp.simplify(sp.diff(L_K, v))

    print(f"  dL_K/du = {dLK_du}")
    print(f"  dL_K/dv = {dLK_dv}")
    print()

    # Critical point of L_K on simplex interior:
    # -1/u + 1/(2(1-u/2-v)) = 0  => 1/u = 1/(2-u-2v)
    # => 2-u-2v = u => u = 1-v
    # 1/(1-u/2-v) = 0 ... no solution.
    # Actually: dL_K/dv = 1/(1-u/2-v), which is always positive.
    # So L_K is increasing in v: minimize at v=0.
    # dL_K/du|_{v=0} = -1/u + 1/(2(1-u/2)) = -1/u + 1/(2-u)
    # Set to 0: 1/u = 1/(2-u) => u = 2-u => u = 1

    print("Static saddle of L_K:")
    print("  dL_K/dv > 0 always => minimize at v=0")
    print("  dL_K/du|_{v=0} = -1/u + 1/(2-u) = 0 => u = 1")
    print("  => Saddle at (1, 0), a vertex")
    print(f"  L_K(1,0) = -log(1 * 1/2) = {-np.log(0.5):.6f} = log(2)")
    print()

    # For the symmetrized kernel K_s:
    # K_s(P,Q) = (1/2)[K(P;Q) + K(Q;P)]
    # The total comparable area A(u,v) = (K1)(u,v) + (K^T 1)(u,v)
    # where (K^T 1)(u,v) = v(1-v-u) (region b from Part 1)

    print("Symmetrized action:")
    print("  L_s(u,v) = -log A(u,v) = -log[u(1-u/2-v) + v(1-v-u)]")
    print("  This is the action computed in Parts 1-5.")
    print()

    # Final summary
    print("=" * 70)
    print("SUMMARY: Action Functional S[u,v] for d=2 Surface Theory")
    print("=" * 70)
    print()
    print("Transfer operator on simplex Sigma = {u,v >= 0, u+v <= 1}:")
    print("  (Kf)(u,v) = int_0^u int_v^{1-u'} f(u',v') dv' du'")
    print()
    print("Comparable area (symmetrized):")
    print("  A(u,v) = u(1-u/2-v) + v(1-v-u)")
    print("         = u + v - u^2/2 - v^2 - 2uv")
    print()
    print("Action functional for path gamma(t) = (u(t), v(t)):")
    print("  S[gamma] = -int_0^T log A(u(t), v(t)) dt")
    print()
    print("Euler-Lagrange (static): dA/du = dA/dv = 0")
    print("  => u* = 0, v* = 1/2 (boundary saddle)")
    print()
    print("Hessian of A is indefinite: A has no interior maximum.")
    print("  A_uu = -1, A_vv = -2, A_uv = -2, det(H) = -2 < 0")
    print()
    print("WKB connection: psi ~ exp(-S) => S_u * S_v = mu = 1/gamma_2")
    print("  Full eigenvalue gamma_2 = 0.2764 from Galerkin computation.")
    print()
    print("The action functional captures the geometry of the constrained")
    print("surface: paths are weighted by the volume of comparable cones,")
    print("and the spectral gap gamma_2 emerges from the full path integral,")
    print("not from any single saddle point.")


# ===========================================================================
# Main
# ===========================================================================

if __name__ == "__main__":
    verify_comparable_area()
    display_grids()
    crit = symbolic_derivation()
    discrete_path_weights()
    saddle_point_analysis()
    transition_density()
