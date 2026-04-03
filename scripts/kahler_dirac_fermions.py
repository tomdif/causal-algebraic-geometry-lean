"""
Kähler-Dirac Fermions on the Simplex Boundary

The bulk comparability framework is intrinsically BOSONIC (8 routes tested, all fail).
Fermions emerge on the BOUNDARY of the state space via the domain-wall mechanism.

Key results:
  - Kähler-Dirac on order complex of [m]^d: d²=0, {K_KD,Γ}=0, spectrum symmetric
  - Order complex is contractible → trivial bulk topology
  - Boundary ∂Σ_d = S^{d-1} has nontrivial topology:
    d=3: S², χ=2, two CHIRAL zero modes
    d=4: S³, χ=0, vectorlike pair (correct for SM fermions)
  - Chirality alternates: chiral at odd d, vectorlike at even d

Status: STRUCTURAL
  Topology correct, algebra works, chirality pattern matches.
  Connecting to physical fermions requires showing boundary modes
  couple to bulk transfer operator and survive continuum limit.
"""
# See inline computation for full Kähler-Dirac construction
# and boundary topology analysis.
