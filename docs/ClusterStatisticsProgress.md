# Cluster statistics: a conditional area criterion and larger-box tests

## Outcome

The new formal result is an event-probability bound, not an area-law proof.
For two independent uniform trimmed profiles, let `c` count the connected
disagreement regions after pointwise sorting. If

```
p = P_I(c <= K) > 0,
```

then Lean proves

```
W <= K log 2 - log p.
```

Consequently, in four ambient dimensions, the two hypotheses

```
K <= A m^2,       P_I(c <= K) >= exp(-B m^2)
```

imply `W <= (A log 2 + B)m^2`. The event need not be typical: an
area-exponentially small probability would suffice. Neither hypothesis
has been established uniformly in box side for this model.

Fixed-size sampling through side eight gives reason to be cautious about
the earlier mean-cluster shortcut. The independent-profile mean divided
by `m^2` rises across these boxes, whereas the uniform-ordered mean,
which supplies only a lower entropy bound, eventually falls. The
experiments do not determine either asymptotic growth rate.

This is a formalized elementary probability inequality and a tested
research instrument. No claim of literature novelty, a mathematical
breakthrough, or gravitational dynamics is made.

## Formal proof and scope

Continue the definitions in [the cluster note](OrderingClusterProgress.md):
`H` counts antitone profiles on `[m]^d` with heights `0,...,m-1`,
`Q` counts weakly ordered pairs, and `W=log(H^2/Q)`. The previous exact
switching identity gives

```
E_I[2^(-c)] = Q/H^2 = exp(-W).
```

On `c <= K`, the integrand is at least `2^(-K)`. Hence
`exp(-W) >= p 2^(-K)`; taking logarithms proves the bound.

[CAGClusterStatistics.lean](../CausalAlgebraicGeometry/CAGClusterStatistics.lean)
defines the probability as an explicit finite sum, proves it lies in
`[0,1]` for positive side, and proves the entropy inequality. It also
checks the deterministic support bound `0 <= c <= m^d`, used below
for bounded-observable confidence intervals.

The area criterion is a theorem **with hypotheses**, not a conclusion
that the area law holds. Combining it with the previously proved trimming
bound would give

```
Delta_4 = T_4 + W_4
        <= (2 log 16 + A log 2 + B)m^2.
```

Even that would only be an upper bound. A positive limiting coefficient
`Delta_4/m^2 -> sigma > 0` would require further work. The unconditional
total-deficit upper bound remains `O(m^(5/2))`.

## Sampling the correct two ensembles

The [C++ sampler](../scripts/cluster_cftp.cpp) uses monotone heat-bath
coupling from the past (CFTP). It extends the update history backward
while retaining every previously generated update at its original time,
then replays that history from both extreme profiles. Agreement couples
every starting profile, removing the need to choose a burn-in length.
This is the construction of
[Propp and Wilson (1996)](https://www.stat.berkeley.edu/~aldous/206-RWG/RWGpapers/propp_wilson.pdf).

For a selected base point the allowed height interval is

```
[max(successor heights, 0), min(predecessor heights, m-1)].
```

Set `L=lcm(1,...,m)` and draw an integer `u` uniformly in `0,...,L-1`.
The update `lo + floor(u*(hi-lo+1)/L)` is exactly uniform on that
interval, since every possible interval length divides `L`.
The same quantile couples ordered starting profiles monotonically.
Heat-bath transitions satisfy detailed balance with the uniform measure;
single-site paths connect the state space, and self-loops give aperiodicity.

The two modes are deliberately different:

- Independent ensemble `I`: two separately coupled uniform profiles on
  `[m]^3`, followed by sorting.
- Ordered ensemble `O`: one coupled uniform profile on
  `[m]^3 x [2]`, with the same height range, split into its two ordered
  layers. Sorting independent profiles would NOT sample this ensemble.

Connected components are counted using overlapping bands along immediate
base edges, justified by the prior cover-edge locality theorem.

Exact sampling and statistical coverage are mathematical statements
under ideal independent uniform randomness. The implementation uses
`mt19937_64`, is not Lean-verified, and is not claimed to produce literal
independent randomness. A horizon cap aborts the entire experiment on
failure; it never replaces difficult draws. All reported batches completed.
The coverage statement concerns errors in a report under the ideal model,
not coverage conditional on completing a resource-capped run.

## Fixed-size results

Each ensemble uses 4,000 pairs at each preselected side
`2,3,4,6,8`: 40,000 pair samples in total. Reproducibility reruns used
the same seeds and reproduced all cluster histograms; those reruns are
not counted as additional independent evidence.

| Side m | Sample mean c / m^2, independent I | Sample mean c / m^2, ordered O | Interval for W / m^2 |
|---:|---:|---:|---:|
| 2 | 0.348313 | 0.281438 | [0.2080, 0.2293] |
| 3 | 0.483611 | 0.292917 | [0.2533, 0.2857] |
| 4 | 0.600828 | 0.234000 | [0.2457, 0.3584] |
| 6 | 0.841500 | 0.143653 | [0.1439, 0.4552] |
| 8 | 1.096480 | 0.107902 | [0.0813, 0.5860] |

Interval endpoints are rounded outward. These are finite statistical
intervals, not Lean-certified numerical enclosures. The joint confidence
construction below applies to all listed boxes and both ensembles.
At sides two and three, the exact ordering costs
`0.867500568` and `2.377004370` lie in their respective intervals.

The independent sample mean divided by `m^3` is approximately
`0.1742, 0.1612, 0.1502, 0.1403, 0.1371`. This finite pattern makes a
bulk-scale mean worth investigating; it does not prove bulk growth or
disprove an eventual `O(m^2)` bound. More importantly, even a bulk-scale
independent mean would not disprove an area-scale `W`: the exact formula
uses `-log E_I[2^(-c)]`, not `(log 2) E_I[c]`.

At side eight the selected low-cluster event is `c <= 47`. Its observed
frequency is `0.0505`; the simultaneous lower confidence bound is
`0.00728572...`. Substituting this lower bound into the formal inequality
gives the statistical upper bound `W <= 37.4998`, compared with
`51.1897` from the independent mean. This is a useful finite improvement,
not an all-side theorem.

At sides six and eight, the inverse-moment confidence interval includes
zero. Directly taking minus the logarithm therefore supplies no finite
upper confidence bound; the reported upper bounds use the event method.
The raw plug-in estimates are retained in the data but should not be
mistaken for reliable large-box entropy measurements. The corresponding
ordered exponential moment can also be dominated by rare observations;
the ordered report deliberately does not estimate entropy with it.

## Uncertainty calculation

The [Python wrapper](../scripts/cluster_sampling_probe.py) computes
two-sided empirical-Bernstein intervals for `c` and `2^(-c)`, using the
unbiased sample variance and their deterministic ranges. For an observable
in `[0,R]`, the radius is

```
sqrt(2 s^2 log(4/delta)/n) + 7 R log(4/delta)/(3(n-1)).
```

This follows by applying Theorem 4 in
[Maurer and Pontil (2009)](https://arxiv.org/abs/0907.3740) to the
normalized observable and its complement, splitting the error budget
between the two directions. Hoeffding's inequality and a finite union
bound give simultaneous coverage of every threshold `K=0,...,m^3`:

```
P_I(c <= K) >= empirical_CDF(K)
               - sqrt(log(2(m^3+1)/delta)/(2n)).
```

Thus selecting the best threshold after seeing the data is covered by the
same bound. No sample-size stopping rule or asymptotic fit is used.

Each saved ensemble report has total failure budget `0.005`. The
independent budget is split across five sides and three methods; the
ordered budget is split across five mean estimates. A union bound gives
at least 99% simultaneous coverage for the combined reports in the ideal
randomness model. This external statistical argument, ordinary
floating-point evaluations, and the sampler are outside Lean's trust
boundary. The same qualification applies to the table and finite
side-eight improvement.

## Reproduction and verification

Requires Python 3 and a C++17 compiler; no third-party Python package is
needed. Run from the repository root:

```sh
python3 scripts/cluster_sampling_probe.py --sides 2 3 4 6 8 --pairs 4000 --failure-probability 0.005 --include-raw
python3 scripts/cluster_sampling_probe.py --sides 2 3 4 6 8 --pairs 4000 --ensemble ordered --seed 20261006 --failure-probability 0.005 --include-raw
python3 -m unittest discover -s scripts -p 'test_*probe.py' -v
lake build
```

Saved reports include raw cluster and profile-volume histograms, seeds,
sample counts, coupling-work totals, and the source hash:
[independent report](data/cluster_sampling_independent.json) and
[ordered report](data/cluster_sampling_ordered.json). Timing varies on
rerun; seeded replay also depends on the standard library's implementation
of integer sampling.

The sampler source SHA-256 for both recorded runs is
`47fe5ae358c6dae72712c33ba5427cac672f4dfc8a51377a2ebbbde825dd343c`.

Verification checks the actual C++ update, not merely a Python reimplementation:
exhaustive interval uniformity and monotonicity for sides 1–12; exhaustive
small-state detailed balance, connectivity, self-loops, and monotone
coupling; and comparison of column component counts with an independent
unit-cell flood fill for every small-state pair. Separate tests check
seed replay, known small-box ensemble frequencies, the confidence formula,
the event inequality against exact counts, and malformed or uninformative
batches.

The full default Lean build passes (3,488 jobs), and all 18 probe tests
pass. Three new guarded `FinalCheck` endpoints audit the support bound,
the entropy event bound, and the conditional area criterion, depending
only on `propext`, `Classical.choice`, and `Quot.sound`.
No proof placeholders or new mathematical axioms were added to these
results. Existing unrelated build warnings remain.

## Next question, and the gravitational limit

The more promising target now is a quantitative low-cluster event,
rather than a pointwise cluster bound or a sharp identification of entropy
with either ensemble's mean. A next numerical step would be a validated
rare-event method, such as staged conditioning, with its normalizations
and uncertainties tracked. That method has not been implemented here.

An all-side probability bound would still address only this combinatorial
entropy model. Robust boundary locality, a source-dependent interaction,
temperature, and a physical continuum limit remain absent. These results
do not derive attraction, Newton's constant, an inverse-square force, or
Einstein's equations.
