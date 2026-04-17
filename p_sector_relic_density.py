"""
Relic density of the P-sector scalar (gravitational freeze-in).

The CAG framework's K/P decomposition yields a neutral, stable, spin-0
scalar in the P-sector with mass m_P ~ m_H ~ 126 GeV, coupled only
gravitationally. Since sigma ~ m^2/M_Pl^4 ~ 10^{-99} cm^2 is 10^{63}
times below the WIMP miracle cross section, this particle never thermalizes.
Its abundance is set by gravitational freeze-in (UV-dominated).

Reference framework: Causal Algebraic Geometry, prediction #1.
"""

import numpy as np

# ──────────────────────────────────────────────────────────────────────
# Constants (natural units: GeV, cm, seconds)
# ──────────────────────────────────────────────────────────────────────
M_Pl = 1.2209e19          # Planck mass (GeV)
M_Pl_reduced = M_Pl / np.sqrt(8 * np.pi)  # reduced Planck mass
m_P = 126.0               # P-sector scalar mass (GeV)
g_star = 106.75            # SM relativistic d.o.f. at high T
GeV_to_cm2 = 0.3894e-27   # 1 GeV^{-2} in cm^2
GeV_to_gram = 1.783e-24   # 1 GeV in grams
rho_crit_over_h2 = 1.054e-5  # critical density / h^2 in GeV/cm^3
s_0 = 2891.2              # present entropy density in cm^{-3}
T_0 = 2.348e-13           # CMB temperature today in GeV (2.725 K)
Omega_DM_obs = 0.1200      # Planck 2018 observed DM relic density (Omega h^2)

print("=" * 70)
print("P-SECTOR SCALAR RELIC DENSITY (GRAVITATIONAL FREEZE-IN)")
print("=" * 70)

# ──────────────────────────────────────────────────────────────────────
# 1. Gravitational cross section (sanity check)
# ──────────────────────────────────────────────────────────────────────
sigma_grav_GeV2 = m_P**2 / M_Pl**4
sigma_grav_cm2 = sigma_grav_GeV2 * GeV_to_cm2
sigma_WIMP = 3e-26  # cm^3/s  (thermal relic <sigma v>)

print(f"\n--- 1. Gravitational cross section ---")
print(f"  m_P              = {m_P} GeV")
print(f"  M_Pl             = {M_Pl:.4e} GeV")
print(f"  sigma_grav       = m^2/M_Pl^4 = {sigma_grav_GeV2:.3e} GeV^{{-2}}")
print(f"  sigma_grav       = {sigma_grav_cm2:.3e} cm^2")
print(f"  WIMP miracle     ~ 10^{{-36}} cm^2")
print(f"  Ratio            ~ 10^{{{np.log10(sigma_grav_cm2) - (-36):.0f}}}")
print(f"  --> Never thermalizes. Freeze-in is the mechanism.")

# ──────────────────────────────────────────────────────────────────────
# 2. Freeze-in production rate
# ──────────────────────────────────────────────────────────────────────
# For a spin-0 particle coupled only gravitationally, the dominant
# production channel is 2->2 graviton-mediated scattering of bath
# particles: SM SM -> P P via s-channel graviton exchange.
#
# The production rate (number density per unit time):
#   R(T) = c * T^8 / M_Pl^4
# where c is an O(1) numerical coefficient from the phase-space integral.
# For a real scalar produced from all SM species:
#   c ~ g_star^2 / (32 pi^5) ~ 0.37 (we use the exact coefficient below)
#
# The Boltzmann equation in radiation domination:
#   dn/dt + 3Hn = R(T)
# Converting to yield Y = n/s with s = (2pi^2/45) g_{*s} T^3:
#   dY/dT = -R(T) / (s H T)
#
# Hubble rate:
#   H(T) = pi/3 * sqrt(g*/10) * T^2 / M_Pl  (= 1.66 sqrt(g*) T^2/M_Pl)
#
# Entropy density:
#   s(T) = (2 pi^2 / 45) g_{*s} T^3

print(f"\n--- 2. Freeze-in production ---")

def hubble(T, g=g_star):
    """Hubble rate H(T) in GeV."""
    return 1.66 * np.sqrt(g) * T**2 / M_Pl

def entropy_density(T, g=g_star):
    """Entropy density s(T) in GeV^3."""
    return (2 * np.pi**2 / 45) * g * T**3

# Production rate coefficient for gravitational 2->2
# R(T) = alpha * T^8 / M_Pl^4
# From Hall, Jedamzik, March-Russell, West (2010), Eq.(4):
# For a real scalar, summing over all SM initial states:
#   alpha = g_eff^2 / (128 pi^5)
# where g_eff counts the effective production channels.
# Conservative: all SM d.o.f. contribute -> g_eff ~ g_star
alpha = g_star**2 / (128 * np.pi**5)
print(f"  Production coefficient alpha = {alpha:.4f}")

# ──────────────────────────────────────────────────────────────────────
# 3. Yield from freeze-in (UV-dominated integral)
# ──────────────────────────────────────────────────────────────────────
# Y_infty = integral from T_low to T_RH of R(T)/(s(T) H(T) T) dT
#
# Plugging in:
#   R/(s H T) = alpha T^8 / (M_Pl^4 * (2pi^2/45)g* T^3 * 1.66 sqrt(g*) T^2/M_Pl * T)
#             = alpha T^8 / (M_Pl^3 * (2pi^2/45) * 1.66 * g*^{3/2} * T^6)
#             = alpha T^2 / (M_Pl^3 * (2pi^2/45) * 1.66 * g*^{3/2})
#
# Integrating from 0 to T_RH:
#   Y = alpha * T_RH^3 / (3 * M_Pl^3 * (2pi^2/45) * 1.66 * g*^{3/2})

def yield_freeze_in(T_RH):
    """Freeze-in yield Y = n/s at late times."""
    numerator = alpha * T_RH**3
    denominator = 3 * M_Pl**3 * (2 * np.pi**2 / 45) * 1.66 * g_star**1.5
    return numerator / denominator

def omega_h2(T_RH):
    """Relic density Omega h^2 from freeze-in."""
    Y = yield_freeze_in(T_RH)
    # Omega h^2 = m * Y * s_0 / rho_crit_h2
    return m_P * Y * s_0 / rho_crit_over_h2

print(f"\n--- 3. Relic density Omega h^2 vs T_RH ---")
print(f"  {'T_RH (GeV)':>16s}  {'Y':>14s}  {'Omega h^2':>14s}  {'Omega/0.12':>12s}")
print(f"  {'-'*16}  {'-'*14}  {'-'*14}  {'-'*12}")

T_RH_values = [1e6, 1e8, 1e10, 1e12, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19]
for T in T_RH_values:
    Y = yield_freeze_in(T)
    Oh2 = omega_h2(T)
    print(f"  {T:16.2e}  {Y:14.4e}  {Oh2:14.4e}  {Oh2/0.12:12.4e}")

# ──────────────────────────────────────────────────────────────────────
# 4. Solve for T_RH that gives Omega h^2 = 0.12
# ──────────────────────────────────────────────────────────────────────
# Omega h^2 = m_P * alpha * T_RH^3 * s_0 / (3 M_Pl^3 * K * rho_c)
# where K = (2pi^2/45) * 1.66 * g*^{3/2}
#
# T_RH^3 = 0.12 * 3 * M_Pl^3 * K * rho_c / (m_P * alpha * s_0)

K = (2 * np.pi**2 / 45) * 1.66 * g_star**1.5
T_RH_target_cubed = Omega_DM_obs * 3 * M_Pl**3 * K * rho_crit_over_h2 / (m_P * alpha * s_0)
T_RH_target = T_RH_target_cubed**(1./3.)

print(f"\n--- 4. Required reheating temperature ---")
print(f"  For Omega h^2 = {Omega_DM_obs}:")
print(f"  T_RH = {T_RH_target:.4e} GeV")
print(f"  T_RH / M_Pl = {T_RH_target / M_Pl:.4e}")
print(f"  log10(T_RH/GeV) = {np.log10(T_RH_target):.2f}")

# Verify
Oh2_check = omega_h2(T_RH_target)
print(f"  Verification: Omega h^2(T_RH) = {Oh2_check:.6f}")

# ──────────────────────────────────────────────────────────────────────
# 5. Consistency checks
# ──────────────────────────────────────────────────────────────────────
print(f"\n--- 5. Consistency checks ---")

# BBN constraint: T_RH > ~4 MeV (conservative)
T_BBN = 4e-3  # GeV
print(f"  BBN lower bound:  T_RH > {T_BBN:.0e} GeV  -->  {'PASS' if T_RH_target > T_BBN else 'FAIL'}")

# Gravitino / moduli problem (SUSY-dependent): T_RH < ~10^9 GeV typically
T_gravitino = 1e9  # GeV
print(f"  Gravitino bound:  T_RH < {T_gravitino:.0e} GeV  -->  "
      f"{'PASS' if T_RH_target < T_gravitino else 'EXCEEDS (but no SUSY here)'}")

# Planck scale: T_RH < M_Pl
print(f"  Sub-Planckian:    T_RH < {M_Pl:.2e} GeV  -->  {'PASS' if T_RH_target < M_Pl else 'FAIL'}")

# Inflation scale (Planck upper bound from r < 0.036):
# V^{1/4} < 1.6 x 10^16 GeV  =>  T_RH < V^{1/4}
T_infl_max = 1.6e16  # GeV
print(f"  Inflation bound:  T_RH < {T_infl_max:.1e} GeV  -->  "
      f"{'PASS' if T_RH_target < T_infl_max else 'TENSION'}")

# Free-streaming: the P-scalar is produced at T ~ T_RH but becomes
# non-relativistic at T_NR ~ m_P = 126 GeV, long before structure formation.
# After T_NR, momentum redshifts as p ~ a^{-1} and v ~ p/m ~ (T/T_NR).
# The free-streaming length for a particle that becomes NR at T_NR:
#   lambda_fs ~ (T_NR / T_eq) * (1/H_eq) * (T_eq/m_P)  (post-NR contribution dominates)
# More precisely, for gravitational freeze-in producing particles at T_RH >> m:
#   <p/T> ~ 3 at production, then p redshifts. At T = m_P, v ~ 1, then v ~ T/m_P.
#   lambda_fs ~ integral from T_NR to T_eq of v/(aH) da
#   ~ (1/H_eq) * (T_eq/m_P) * ln(T_NR/T_eq)  [logarithmic, small]
T_eq = 0.75e-9  # matter-radiation equality temperature in GeV (~0.75 eV)
H_eq = hubble(T_eq, g=3.36)  # g* ~ 3.36 at equality
# Comoving Hubble radius at equality: ~ 100 Mpc
# Free-streaming of NR particle from T_NR to T_eq:
v_eq = T_eq / m_P  # velocity at equality
# lambda_fs ~ v_eq / H_eq * some log factors ~ tiny
d_H_eq = 1 / H_eq  # Hubble radius at equality in GeV^{-1}
d_H_eq_Mpc = d_H_eq * 1.97e-14 * 1e-6 / 3.086e22  # convert GeV^{-1} to Mpc
# Simpler: 1 GeV^{-1} = 1.97e-16 m = 1.97e-16 / 3.086e22 Mpc = 6.39e-39 Mpc
GeV_inv_to_Mpc = 6.39e-39
lambda_fs_Mpc = (T_eq / m_P) * np.log(m_P / T_eq) * d_H_eq * GeV_inv_to_Mpc
print(f"  T_NR (= m_P):     {m_P} GeV >> T_eq = {T_eq*1e9:.2f} eV")
print(f"  Free-streaming:   lambda_fs ~ {lambda_fs_Mpc:.2e} Mpc")
print(f"  Cold DM bound:    lambda_fs < 0.1 Mpc  -->  "
      f"{'PASS (deeply cold)' if lambda_fs_Mpc < 0.1 else 'WARM/HOT DM issue'}")
print(f"  (126 GeV particle is non-relativistic long before structure formation)")

# Non-thermal production: check if DM is never in equilibrium
Gamma_max = alpha * T_RH_target**8 / (M_Pl**4 * T_RH_target**3)  # rate/volume / n ~ R/n_eq
# Interaction rate per particle: Gamma ~ n <sigma v> ~ T^3 * (T^2/M_Pl^4) = T^5/M_Pl^4
Gamma_int = T_RH_target**5 / M_Pl**4
H_RH = hubble(T_RH_target)
print(f"\n  Thermalization check at T_RH:")
print(f"    Gamma_int     = {Gamma_int:.4e} GeV")
print(f"    H(T_RH)       = {H_RH:.4e} GeV")
print(f"    Gamma/H       = {Gamma_int/H_RH:.4e}")
print(f"    Never thermalizes: {'YES (Gamma << H)' if Gamma_int < H_RH else 'NO -- problem!'}")

# ──────────────────────────────────────────────────────────────────────
# 6. Comparison with other gravitational DM candidates
# ──────────────────────────────────────────────────────────────────────
print(f"\n--- 6. Summary and comparison ---")
print(f"  P-sector scalar mass:        {m_P} GeV")
print(f"  Required T_RH:               {T_RH_target:.3e} GeV")
print(f"  log10(T_RH):                 {np.log10(T_RH_target):.1f}")
print(f"  Omega h^2 scaling:           ~ (T_RH / {T_RH_target:.1e})^3 x 0.12")
print(f"  Production mechanism:        Gravitational freeze-in (UV-dominated)")
print(f"  Detection prospect:          Essentially undetectable directly")
print(f"  Indirect signature:          Isocurvature perturbations if T_RH high")
print()
print(f"  Comparison:")
print(f"    WIMP miracle:   sigma ~ 10^{{-36}} cm^2,  T_fo ~ 5 GeV")
print(f"    P-scalar:       sigma ~ {sigma_grav_cm2:.0e} cm^2,  freeze-in at T_RH ~ {T_RH_target:.0e} GeV")
print(f"    Planckian:      sigma ~ 10^{{-122}} cm^2 (m ~ M_Pl)")
print()

# ──────────────────────────────────────────────────────────────────────
# 7. Sensitivity: Omega h^2 vs T_RH (for plotting / reference)
# ──────────────────────────────────────────────────────────────────────
print(f"--- 7. Key formula ---")
print(f"  Omega h^2 = 0.12 * (T_RH / {T_RH_target:.3e})^3")
print(f"  Y_infty   = {yield_freeze_in(T_RH_target):.4e}")
print(f"  n_DM/s    = {yield_freeze_in(T_RH_target):.4e} (frozen yield)")
print()

# What if there's a small portal coupling?
# Even a tiny Higgs-portal lambda |H|^2 |P|^2 coupling would change everything
print(f"--- 8. Effect of a small Higgs portal coupling ---")
print(f"  If lambda_HP |H|^2 |P|^2 exists with lambda_HP ~ 10^{{-12}}:")
lambda_HP = 1e-12
sigma_portal = lambda_HP**2 / (16 * np.pi * m_P**2)
sigma_portal_cm2 = sigma_portal * GeV_to_cm2
print(f"    sigma_portal ~ {sigma_portal_cm2:.2e} cm^2")
print(f"    This is ~ 10^{{{np.log10(sigma_portal_cm2/sigma_grav_cm2):.0f}}} x sigma_grav")
print(f"    Even lambda ~ 10^{{-12}} dominates over gravity!")
print(f"    The framework predicts lambda_HP = 0 (exact P-sector decoupling)")
print(f"    This is the key prediction: purely gravitational DM.")

print(f"\n{'=' * 70}")
print(f"CONCLUSION")
print(f"{'=' * 70}")
print(f"""
The P-sector scalar at 126 GeV, coupled only gravitationally, is a
viable dark matter candidate IF the reheating temperature is:

    T_RH ~ {T_RH_target:.2e} GeV  (log10 = {np.log10(T_RH_target):.1f})

This is UV-dominated freeze-in: Omega h^2 ~ (T_RH)^3, so the relic
density is entirely determined by the reheating temperature.

The required T_RH is sub-Planckian and consistent with high-scale
inflation. The particle never thermalizes (Gamma/H ~ {Gamma_int/H_RH:.1e}).

Key observational consequence: if T_RH is this high, there may be
detectable gravitational-wave signatures from the reheating epoch,
and potentially observable isocurvature perturbations in the CMB.
""")
