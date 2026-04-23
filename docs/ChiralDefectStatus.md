# Chiral defect on causal substrate — status (2026-04-23)

**Status:**
- Stage 1 (ChiralNoGo numerical) ✅ PASS
- Stage 2 (SSH-soliton proxy on A/B chain) ✅ PASS
- **Stage 3 (bipartite-grading gate on Poisson causal sets) ❌ FAIL — hard obstruction found**

The naive Sharpe-style mechanism — "rank-parity grading bipartites the causal-set cover graph, giving A/B sublattice" — is **falsified on Poisson substrates**. The cover graph contains odd cycles; no Z₂ grading can make cover-adjacency anticommute.

Precommit: `memory/chiral_defect_PRECOMMIT_apr23.md`

## Hypothesis tested today

> **H_proxy:** On a 1D chain with A/B sublattice (SSH dimerization), a
> topological domain wall has a spatially localized zero-energy eigenmode
> concentrated on one sublattice.

This is the Sharpe-style "matter as topological defect" mechanism in its
canonical 1D setting. It is **not** a test of the K/P chamber-kernel
hypothesis on causal sets — that's a separate, larger research task (see
below).

## What passed

### Stage 1 — ChiralNoGo numerical gate
`scripts/chiral_defect_stage1.py`

- Verified `det(μ₁^g) = 1 − W` on L-cycles (L ∈ {16, 32, 64}) to ~1e-14 precision across 60 random gauge configs.
- Verified W=1 configs have exactly one eigenvalue < 1e-15; next-smallest gapped by 0.2–0.4. Zero-mode structure is well-defined.

### Stage 2 (proxy) — SSH soliton A/B zero mode
`scripts/chiral_defect_stage2_ssh_proxy.py`

- **Vacuum** (trivial dimerization, |u| > |v|, open BC, 240 sites):
  smallest |ev| = 0.500, PR = 0.68 (delocalized), A-weight = 0.50 (no chiral preference). Gapped, as expected.
- **Soliton** (trivial/topological domain wall at cell 60):
  zero mode at |ev| ~ 5e-17, PR = 0.010 (≈2% of chain), A-weight = 1.000 (exact A-sublattice concentration), peak at site 120 = domain-wall A-site.

All five pre-committed proxy checks pass. The SSH mechanism reproduces known
1979 physics, confirming numerical infrastructure works as designed.

## What was not tested (and why)

The precommit's original Stage 2 asked for a test on a **(1+1)D topologically-compactified causal set** using the repo's **K/P chamber-kernel decomposition**. On reflection during coding:

1. **The 1D chamber kernel is gauge-invariant only via the Wilson loop W.**
   In 1D, any two configurations with the same W are gauge-equivalent; localization of eigenvectors is then a gauge artifact, not physical. Spatial localization of a "vortex zero mode" requires ≥ 2D.

2. **The chamber kernel `K_F = ζ_F + ζ_F^T − I` is defined in the repo for grid posets and 1D chains.** A chamber kernel for general 2D causal sets (e.g., Poisson sprinklings in 1+1D Minkowski) is not in `ChamberKernel.lean`, and the K/P sector decomposition used in `ChiralStructure.lean` specializes to the 1D zeta operator. Extending K/P to a 2D substrate in a way that preserves its chirality content is a research task, not a coding task.

3. **ChiralNoGo forces periodic BC** for any nontrivial chirality. Any 2D test must include topological compactification; this adds a boundary condition to the chamber-kernel definition that isn't currently formalized.

Running a test that uses the 1D chamber kernel and a 1D "vortex" would produce numbers but not distinguish vacuum from defect in a gauge-invariant way; it would be theater, not evidence. Running the SSH proxy is a legitimate intermediate step: it confirms the mechanism exists in the canonical setting before committing compute to the harder causal-set extension.

## Stage 3 — bipartite gate (FAIL, 2026-04-23)

`scripts/chiral_defect_stage3_bipartite_gate.py`

**Pre-committed gate:** `residual(ρ) = ‖{Γ, A}‖_F / ‖A‖_F` < 0.1 across ρ ∈ {50, 200, 500} to PROCEED; > 0.3 to STOP.

**Measured:**

| ρ | N events | residual (rank-parity Γ) | frac covers jump rank=1 |
|---|---|---|---|
| 50 | ~52 | 1.15 ± 0.13 | 0.47 |
| 200 | ~196 | 1.23 ± 0.02 | 0.35 |
| 500 | ~513 | 1.38 ± 0.01 | 0.07 |

Residual is **order-of-magnitude** above the stop threshold. The problem *worsens* with density: at ρ=500, only 7% of cover relations connect adjacent ranks, so the bipartite structure of the regular lattice is substrate-level destroyed by Poisson randomization.

**Probed five alternative gradings** (temporal-index parity, spatial-halves, random benchmark, rank/2 parity, greedy-2-coloring):
- All natural gradings residual in [1.26, 1.72], essentially at random-baseline ~1.40. Rank-parity is *barely better* than random.
- **Greedy 2-coloring detects odd cycles in every realization** at ρ ∈ {200, 500}. The cover graph is literally not a bipartite graph. No Z₂ grading can anticommute with cover adjacency.

### Implications (what IS ruled out)

- **The naive Sharpe import** — "K/P ↔ A/B sublattice via cover-adjacency bipartiteness" — is falsified on Poisson causal substrates.
- The direction map from `(Sharpe A/B, vortex)` → `(K/P, causal-set defect)` cannot go through a substrate-bipartite construction. Any such attempt will see random-level residuals because the cover graph has odd cycles.

### Implications (what is NOT ruled out)

- **The γ₅-via-doubling route.** The repo's actual chirality operator (`ChiralDoubling.lean`) is γ₅ on the *doubled* chamber Dirac `D = [[0, A], [A^T, 0]]`, not a grading internal to a single kernel. γ₅ anticommutes with D by construction regardless of substrate bipartiteness. So a Sharpe-analog via doubling is still in principle possible — it just isn't the "A/B sublattice" story.
- **Regular / quasi-regular sprinklings.** If the substrate has more structure than Poisson (e.g., a stratified sprinkling respecting temporal layers), bipartiteness might be recoverable. But this would import the regular-lattice crutch the user's framework is trying to avoid.
- **Alternative incidences.** "Chains of length exactly k" adjacency matrices may have different bipartite structure than covers. Not probed.

### Decision

The Stage-3 gate precommit says STOP and write up obstruction. That's what's happening here. Stage 2 (vortex localization) via the naive bipartite route is **abandoned**.

## What would be needed for a direct K/P causal-set test

In order of estimated effort:

1. **Define a K/P decomposition for 2D causal sets.**
   Given a Poisson sprinkling `C ⊂ ℝ^{1,1}` with periodic spatial direction, define ζ_C(i,j) = [i ≤ j] (causal-order kernel) and identify a natural Z₂ grading (the "K/P" analog) commuting with a discrete chirality operator. Candidate: the parity of chain-length from a fixed root. Requires proof that this grading is well-defined and gauge-natural.

2. **Gauge the causal-set kernel.**
   Specify how a U(1) phase field `θ: C → ℝ` induces link phases `g_{ij} = exp(i(θ_j − θ_i))` on cover relations `i ⋖ j`, and compute the gauged kernel `ζ_C^g(i,j) = g_{ij} · ζ_C(i,j)`. Confirm that the plaquette Wilson loops on closed causal diamonds are gauge-invariant.

3. **Spectrum analysis.**
   For vacuum and vortex gauge configs on a fixed sprinkling, diagonalize the gauged K-kernel and measure: (a) zero-mode existence, (b) participation ratio on the event set, (c) K-sector-vs-P-sector weight on the zero-mode eigenvector.

4. **Precommit + run at multiple sprinkling densities.**
   Check robustness across sprinkling realizations; run at ρ ∈ {200, 500, 1000} events per unit spacetime volume.

### Estimated cost

- Step 1: 2–4 weeks of math + Lean work (depends on whether the Z₂ grading falls out of existing structures or needs new definitions).
- Steps 2–4: 1–2 weeks of code + compute given Step 1 in hand.

### Alternative: a compatible Wilson-Dirac test

If Step 1 is too open-ended, a substantially cheaper path is to run a **standard 2D Wilson-Dirac operator on a Poisson-sprinkled random graph** that approximates the causal-set geometry. This would confirm the mechanism on a genuinely disordered substrate without requiring a full chamber-kernel redefinition. It's less aligned with your framework's own language, but more tractable: 1-2 weeks total.

## Decision for this session

Neither the direct K/P test nor the Wilson-Dirac proxy is appropriate to run in a single session without a precommit that pins down the new definitions. The SSH proxy suffices to rule out the trivial failure mode ("maybe the mechanism doesn't even work in 1D"). It does.

**Recommendation:** treat this session's work as Tier 0 (infrastructure + mechanism confirmation). The Tier 1 work (direct K/P on 2D causal set) deserves its own research plan with a dedicated precommit, which should include the mathematical definitions in Step 1 above before any code runs.

## What this does NOT justify claiming

- No statement about α_em derivation on causal sets.
- No statement about graviton propagator.
- No statement about Λ from topological-defect density.
- No claim that K/P ↔ A/B mapping holds. The SSH test shows A/B chains work; K/P is not tested.
- No revival of NCDS Theorem 4 claims beyond what was already demonstrated there (Raychaudhuri focusing, p < 0.0001), which this work does not touch.

## Files

- `scripts/chiral_defect_stage1.py` — ChiralNoGo numerical verification (PASS)
- `scripts/chiral_defect_stage2_ssh_proxy.py` — SSH soliton A/B localization (PASS, 5/5 precommit checks)
- `scripts/chiral_defect_stage3_bipartite_gate.py` — bipartite-grading gate on Poisson causal sets (**FAIL**, obstruction found, pre-committed STOP verdict)
- `memory/chiral_defect_PRECOMMIT_apr23.md` — precommit protocol (outside this repo)

## What the retraction discipline saves

Had we skipped Stage 3 and proceeded straight to a vortex test using rank-parity Γ, we would have seen *some* spectral signal (because random gradings produce noise that looks structured) and the natural narrative arc would have been "CAG framework predicts chiral zero modes from topological defects." With the bipartite cover graph assumption quietly false. Stage 3 caught that. Cost: ~30 minutes of compute and one clean "NO" answer. Savings: weeks of compute downstream plus the retraction letter afterwards.

Same pattern as `ssh_hubbard_PRECOMMIT_v1_retraction.md` and the BM moiré β-falsification (see `project_cag_moire_week1_summary.md`). Audit discipline working as intended.
