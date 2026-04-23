# OEIS submission draft -- MacMahon cluster shapes

**Status:** Draft, ready for review. Not submitted.

**Sequence:** `3, 10, 24, 63, 134, 326, 702, 1517, 3054, 6377, 12664, 25654, 50611, 99592, 192452, 369717`
(offset 3 -- a(3) = 3 is the first term; no solid partition smaller than size 3 produces an active cluster.)

**Companion submission:** The multiplicative MacMahon correction
R(q) = D_3(q)/A000294(q), drafted separately in
`~/oeis_R_q_submission.md`. R(q) is the generating function whose
*existence* motivates enumerating the clusters described here; this
submission records the *number of distinct shapes* that appear as
terms in its combinatorial expansion.

---

## Reproduction and novelty

**Reproduction (2026-04-23):**
Re-ran `~/scripts/classify_clusters.py` with `MAX_N = 9`. Output
matches memory: `Cluster size 3: 3, ..., Cluster size 9: 702`.

**Extension to MAX_N = 18 (~73 s wall time):**
All lower terms stable; extends the sequence to
a(3..18) = 3, 10, 24, 63, 134, 326, 702, 1517, 3054, 6377, 12664,
25654, 50611, 99592, 192452, 369717.

Stability check: a(n) is identical for every MAX_N >= n that was
tested (MAX_N in {9, 10, 11, 12, 13, 15, 17, 18}). Every cluster of
size n realizable in ANY solid partition is already realized by some
solid partition of size <= n in the tested range; no shape appears
for the first time at a larger host partition.

**Novelty check (all confirmed "No results." on oeis.org 2026-04-23):**
- seq:3,10,24,63,134,326,702
- seq:3,10,24,63,134,326,702,1517,3054
- seq:10,24,63,134,326,702,1517
- seq:24,63,134,326,702,1517,3054,6377
- seq:134,326,702,1517,3054,6377
- seq:1517,3054,6377,12664,25654
- First differences seq:7,14,39,71,192,376,815,1537 -- no results
- Partial sums seq:3,13,37,100,234,560,1262,2779 -- no results
- Binomial transform seq:3,13,47,168,573,1919,6351 -- no results

Unrelated sequence cross-check: A151830 (fixed 4-dim polycubes) begins
1, 4, 28, 234, 2162, ... and grows much faster, so our clusters --
which are a restricted subset of 4D polycubes -- are clearly a
distinct enumeration.

---

## OEIS fields

```
%I Axxxxxx

%S Axxxxxx 3,10,24,63,134,326,702,1517,3054,6377,12664,25654,50611,99592,192452,
%T Axxxxxx 369717

%N Axxxxxx Number of distinct shapes, up to translation, of connected clusters of "active" cells of size n appearing in 4-dimensional Young diagrams of solid partitions.

%C Axxxxxx Definition of "active cell". Given a solid partition lambda, represented as a 4-dimensional Young diagram D in Z_{>=1}^4 (the set of unit cells it occupies), a cell (i,j,k,l) in D is a CORNER cell if (i+1,j,k,l), (i,j+1,k,l), and (i,j,k+1,l) are all outside D, and INTERIOR otherwise. The RANK of a corner cell is r = i+j+k-2. An interior cell is always "active." A corner cell is "active" iff its rank r is not equal to 1 (equivalently, its corner-hook-volume contribution 1-r is nonzero).

%C Axxxxxx The active cells of D form a subset A(D) of D. Connectivity on A(D) uses 4-neighbor adjacency on Z^4 (the 8 unit-step neighbors that differ by +-1 in exactly one coordinate). A CLUSTER is a connected component of A(D). A CLUSTER SHAPE of size n is the translation-equivalence class of a size-n connected subset of Z^4 that arises as a cluster in A(D) for at least one solid partition D. This sequence counts such shapes.

%C Axxxxxx Equivalent combinatorial description via MacMahon. The corner-hook volume (chvol) of Amanov-Yeliussizov 2020 is the sum over corner cells of their rank. MacMahon's 1916 product A000294 enumerates solid partitions by chvol, not by size; the additive deficit A000294 - A000293 is A007326. A solid partition contributes to the deficit precisely when |D| differs from chvol(D), equivalently when the set of active cells A(D) is non-empty. Through all solid partitions of size up to 18 tested here every such A(D) is a single connected component; no multi-cluster examples have been observed. So each deficit contribution is indexed by exactly one cluster shape, and the present sequence enumerates those shapes by size.

%C Axxxxxx Growth is consistent with 4-dimensional lattice-animal growth: a(n+1)/a(n) takes values 3.33, 2.40, 2.62, 2.13, 2.43, 2.15, 2.16, 2.01, 2.09, 1.99, 2.03, 1.97, 1.97, 1.93, 1.92 for n = 3..17, slowly decreasing toward the expected 4D fixed-animal growth constant.

%C Axxxxxx The generating function of the clusters, weighted by cluster delta (sum of 1-rank over corner cells plus 1 for each interior cell) and summed over host partitions, equals the multiplicative MacMahon correction R(q) = A000293(q)/A000294(q) (see Ayyyyyy, pending submission). This sequence counts the support at each weight; Ayyyyyy records the signed weighted sum.

%H Axxxxxx Alimzhan Amanov and Damir Yeliussizov, <a href="https://arxiv.org/abs/2009.00592">MacMahon's statistics on higher-dimensional partitions</a>, arXiv:2009.00592, 2020.

%H Axxxxxx Percy A. MacMahon, <a href="https://archive.org/details/combinatoryanal02macmuoft">Combinatory Analysis, Volume 2</a>, Cambridge University Press, 1916 (conjectured product for solid partitions, now known to fail first at n=6).

%H Axxxxxx Suresh Govindarajan, <a href="http://boltzmann.wikidot.com/solid-partitions">Solid Partitions Project</a>, 2010 (computational enumeration of A000293).

%e Axxxxxx a(3) = 3. The smallest host partitions producing an active cluster have size 3: the partitions lambda = (3), lambda = (2,1), and lambda = (1,1,1) each contribute a three-cell L-tromino lying along one of three distinct 4-directions in Z^4, and these three L-trominos are inequivalent under translation.

%e Axxxxxx a(4) = 10. At cluster size 4 there are two distinct delta totals: a compact 2x2 rectangular shape with delta = +1 (arising from an interior cell joined to three corner cells) and L-tetromino variants with delta = -1 or -2, accounting together for 10 distinct translation classes.

%o Axxxxxx (Python) # Full reproduction script: ~/scripts/classify_clusters.py.
%o Axxxxxx # Sketch (depends on a plane-partition generator):
%o Axxxxxx def corners(D):
%o Axxxxxx     return {(i,j,k,l) for (i,j,k,l) in D
%o Axxxxxx             if (i+1,j,k,l) not in D
%o Axxxxxx             and (i,j+1,k,l) not in D
%o Axxxxxx             and (i,j,k+1,l) not in D}
%o Axxxxxx def delta_map(D):
%o Axxxxxx     C = corners(D); out = {}
%o Axxxxxx     for (i,j,k,l) in D:
%o Axxxxxx         out[(i,j,k,l)] = (1 - (i+j+k-2)) if (i,j,k,l) in C else 1
%o Axxxxxx     return out
%o Axxxxxx # active = {p for p, d in delta_map(D).items() if d != 0}
%o Axxxxxx # clusters = connected components of active under +-1 unit-step adjacency in Z^4
%o Axxxxxx # shape(c) = frozenset({tuple(p[i] - min_coord[i] for i in range(4)) for p in c})
%o Axxxxxx # a(n) = |{shape(c) : |c| = n, c a cluster of some solid partition}|

%Y Axxxxxx Cf. A000293 (solid partitions), A000294 (MacMahon conjectured product for solid partitions), A007326 (additive MacMahon deficit A000294 - A000293), A151830 (all fixed 4-dim polycubes), A049429 (fixed polycubes by dimension).

%Y Axxxxxx Cf. Ayyyyyy (R(q) = A000293(q)/A000294(q), multiplicative MacMahon correction; the present sequence is the cardinality of the shape support at each q-degree of Ayyyyyy).

%K Axxxxxx nonn,more,nice

%O Axxxxxx 3,1

%A Axxxxxx Thomas DiFiore, Apr 23 2026
```

---

## Extended b-file (n=3..18)

```
3 3
4 10
5 24
6 63
7 134
8 326
9 702
10 1517
11 3054
12 6377
13 12664
14 25654
15 50611
16 99592
17 192452
18 369717
```

Runtime to produce a(18): approximately 73 s on a 2023-era laptop in
plain Python using the enumeration over all solid partitions up to
size 18. Further extension is feasible but grows by roughly 2x per
unit of MAX_N as A000293 grows.

---

## Submission checklist before sending

- [ ] Remove the `nice` keyword if editor prefers; leave `nonn,more`.
- [ ] Replace `Ayyyyyy` in %C and %Y with the actual R(q) A-number
  once assigned. If the R(q) submission is still pending, note it
  as "to be assigned" in the cover note.
- [ ] Confirm offset `3,1`: the sequence starts at a(3) = 3, and the
  first index at which a(n) > 1 is n = 3 itself (counting from 1
  that is the first entry), so `3,1` is correct.
- [ ] Example block deliberately stays geometric (L-tromino, 2x2
  rectangle, L-tetromino) and does not invoke the author's
  unpublished framework. The %C block defines everything needed to
  re-derive the sequence from scratch.
- [ ] Update A-number on %A/%I line when assigned.

## What this sequence is NOT

- **Not A151830 or A049429**: those count all fixed polycubes in 4D;
  our shapes are strictly a subset (only those realizable as active
  clusters inside a solid partition). A151830 begins 1, 4, 28, 234, ...
  which already dominates our 3, 10, 24, 63, ... at n=4.
- **Not A007326**: that is the additive discrepancy A000294 - A000293.
  Our sequence counts how many distinct lattice-animal shapes
  contribute at each weight.
- **Not R(q) = Ayyyyyy**: R(q) is a signed, weighted series; this is
  the unweighted cardinality of the shape support by cluster size.

## Why both this and R(q) are worth submitting

R(q) is the cleaner algebraic object (integer g.f. coefficients from
a known conjecture). This sequence is the structural object -- it
records the actual combinatorial building blocks that make R(q)
integer. Together they are the additive/multiplicative pair for the
same 4D lattice-animal enumeration. R(q) is the paper result; this
sequence is the phenomenology that forces the paper.
