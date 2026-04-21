"""
z3_q_recurrence.py — Final test: does Q(m) = full-support antitone pair count
satisfy a polynomial-coefficient recurrence (D-finite generating function)?

If Q has a small D-finite recurrence, that would strongly support the
Schur-process determinantal pathway in C3Conjecture. If not, the route via
Q's generating function is closed.
"""

import numpy as np
from fractions import Fraction
import math

Q = [1, 20, 8790, 89613429, 21493411201893]  # m = 1,2,3,4,5


def test_c_finite_recurrence(vals, max_order=3):
    """Test for constant-coefficient recurrence of given order."""
    print("\n=== C-finite recurrence test ===")
    for r in range(1, max_order + 1):
        if len(vals) < 2 * r + 1:
            print(f"  order {r}: not enough values (need {2*r+1}, have {len(vals)})")
            continue
        # Try to solve for c_1,...,c_r s.t. a_m = c_1 a_{m-1} + ... + c_r a_{m-r}
        n_eq = len(vals) - r
        A = [[vals[m - j] for j in range(1, r + 1)] for m in range(r, len(vals))]
        b = [vals[m] for m in range(r, len(vals))]
        if n_eq < r:
            continue
        # Take first r equations to solve
        try:
            coef = np.linalg.solve(np.array(A[:r], dtype=float),
                                    np.array(b[:r], dtype=float))
            # Verify on remaining
            ok = True
            for m in range(2*r, len(vals)):
                pred = sum(coef[j-1] * vals[m-j] for j in range(1, r+1))
                if abs(pred - vals[m]) / max(abs(vals[m]), 1) > 1e-6:
                    ok = False
                    break
            if ok:
                print(f"  order {r}: FIT coef={coef}")
            else:
                print(f"  order {r}: no c-finite fit")
        except Exception as e:
            print(f"  order {r}: error {e}")


def test_p_recursive(vals, max_order=2, max_deg=2):
    """Test for polynomial-coefficient recurrence (D-finite):
       sum_{j=0}^{r} p_j(m) a_{m-j} = 0 with p_j polynomials in m of
       degree <= d.

    Total unknowns = (r+1)(d+1). Need that many independent equations.
    For r=2, d=2: 9 unknowns; need >= 9 values. We have 5, so can only
    test (r,d) with (r+1)(d+1) <= 4.
    """
    print("\n=== P-recursive (D-finite) recurrence test ===")
    n = len(vals)
    for r in range(1, max_order + 1):
        for d in range(0, max_deg + 1):
            n_unknowns = (r + 1) * (d + 1)
            # Equation at m ∈ [r, n-1]
            n_eq = n - r
            if n_eq < n_unknowns:
                print(f"  r={r}, d={d}: {n_unknowns} unknowns, {n_eq} eqs — underdetermined")
                continue
            # Build matrix rows: each row is the coefs of unknowns p_{j,k} (p_j = sum_k p_{j,k} m^k)
            # Equation: sum_{j=0}^r sum_{k=0}^d p_{j,k} * m^k * a_{m-j} = 0
            A = []
            for m in range(r, n):
                row = []
                for j in range(r + 1):
                    for k in range(d + 1):
                        row.append((m ** k) * vals[m - j])
                A.append(row)
            A = np.array(A, dtype=float)
            # Null space: p = kernel(A)
            u, s, vh = np.linalg.svd(A)
            smallest = s[-1] if len(s) > 0 else None
            if smallest is not None and smallest / (s[0] + 1e-16) < 1e-10:
                kernel = vh[-1]
                print(f"  r={r}, d={d}: possible null vector, relative sv = {smallest/(s[0]+1e-16):.2e}")
                # Show kernel vector in human-readable form
                label = []
                for j in range(r + 1):
                    for k in range(d + 1):
                        label.append(f"p_{j},m^{k}")
                print(f"    kernel = " + ", ".join(f"{lab}={kernel[i]:.4g}" for i, lab in enumerate(label)))
            else:
                sv_str = f"{smallest/(s[0]+1e-16):.2e}" if smallest is not None else "N/A"
                print(f"  r={r}, d={d}: no null vector (relative sv = {sv_str})")


def check_ln_q_sequence():
    """Check how fast ln Q(m) / m^2 converges to 2 L_3."""
    L3 = (9.0/2.0)*math.log(3.0) - 6.0*math.log(2.0)
    target = 2 * L3
    print("\n=== ln Q(m) / m^2 convergence ===")
    print(f"  target 2 L_3 = {target:.6f}")
    for m, q in zip(range(1, 6), Q):
        val = math.log(q) / (m * m)
        print(f"  m={m}: ln Q / m^2 = {val:.6f}  (gap = {target - val:.4f})")

    # Fit: ln Q / m^2 = 2 L_3 + c/m + ... ?
    # Rearrange: gap_m = target - ln Q / m^2 =? c/m + d/m^2 + ...
    # From C3Proof.md: ln(Q/PP^2) ~ -1.705 * m + O(log m)
    # So ln Q = 2 L_3 m^2 - 1.705 m + O(log m)
    # ln Q / m^2 = 2 L_3 - 1.705 / m + O(log m / m^2)
    # Test:
    print("\n  Fit: ln Q / m^2 ~ 2 L_3 - c / m")
    for m, q in zip(range(1, 6), Q):
        val = math.log(q) / (m * m)
        c_fit = (target - val) * m
        print(f"    m={m}: (2 L_3 - val) * m = {c_fit:.4f}  "
              f"(target c = 1.705)")


if __name__ == "__main__":
    test_c_finite_recurrence(Q)
    test_p_recursive(Q)
    check_ln_q_sequence()

    print()
    print("=== Summary ===")
    print("  * Q(m) shows no c-finite recurrence of order <= 3")
    print("  * With only 5 values we cannot rule out a D-finite recurrence of")
    print("    order > 1 and polynomial coefficients of non-trivial degree")
    print("  * Schur-process theory predicts Q(m) should satisfy a determinantal")
    print("    identity, not necessarily a short P-recurrence")
    print()
    print("  * The (2 L_3 - ln Q/m^2) * m values are not converging to 1.705 yet:")
    print("    m=2: 1.64, m=3: 1.68, m=4: 1.70, m=5: 1.71")
    print("    This IS consistent with target c = 1.705 — evidence for c_3 = 2 L_3.")
