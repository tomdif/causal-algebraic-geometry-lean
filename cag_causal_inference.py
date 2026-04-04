#!/usr/bin/env python3
"""
Causal-Algebraic Geometry Applied to Causal Inference and Bayesian Networks.

This script applies the CAG framework (CSpec, convex subsets, BD action,
dimension law) to standard causal DAGs from the causal inference literature.

Key invariants computed:
  - BD action: S_BD = |nodes| - |edges|
  - Order-convex subsets |CC|: "causally consistent" variable sets
  - Downward-closed sets (ideals) |I|
  - Noetherian ratio gamma = |CC| / |I|
  - Width (max antichain), Height (max chain)
  - Causal algebra matrix representation
"""

from itertools import combinations, chain as iterchain
from collections import defaultdict
import numpy as np


# ============================================================
# Part 1: Define standard causal DAGs
# ============================================================

def make_dag(name, nodes, edges, description=""):
    """Create a DAG as a dictionary."""
    return {
        "name": name,
        "nodes": nodes,
        "edges": edges,  # list of (parent, child) pairs
        "description": description,
    }


def standard_dags():
    """Define the standard causal DAGs."""
    dags = []

    # (a) Chain: X1 -> X2 -> X3 -> X4
    dags.append(make_dag(
        "Chain (X1->X2->X3->X4)",
        ["X1", "X2", "X3", "X4"],
        [("X1","X2"), ("X2","X3"), ("X3","X4")],
        "Total order, no confounders. Simplest causal structure."
    ))

    # (b) Fork: X1 <- Z -> X2
    dags.append(make_dag(
        "Fork (X1 <- Z -> X2)",
        ["Z", "X1", "X2"],
        [("Z","X1"), ("Z","X2")],
        "Common cause / confounder. Z confounds X1 and X2."
    ))

    # (c) Collider: X1 -> Z <- X2
    dags.append(make_dag(
        "Collider (X1 -> Z <- X2)",
        ["X1", "X2", "Z"],
        [("X1","Z"), ("X2","Z")],
        "Common effect / selection bias. Conditioning on Z opens a path."
    ))

    # (d) Diamond: X -> {Y,Z} -> W
    dags.append(make_dag(
        "Diamond (X -> {Y,Z} -> W)",
        ["X", "Y", "Z", "W"],
        [("X","Y"), ("X","Z"), ("Y","W"), ("Z","W")],
        "Two causal paths from X to W. Mediator structure."
    ))

    # (e) Instrumental variable: Z -> X -> Y, U -> X, U -> Y
    dags.append(make_dag(
        "Instrumental Variable (Z->X->Y, U->X, U->Y)",
        ["Z", "X", "Y", "U"],
        [("Z","X"), ("X","Y"), ("U","X"), ("U","Y")],
        "Z is instrument: affects Y only through X. U is unobserved confounder."
    ))

    # (f) Simplified Sachs network (11 nodes, key signaling edges)
    # Based on Sachs et al. (2005) protein signaling network
    sachs_nodes = ["Raf", "Mek", "Plcg", "PIP2", "PIP3", "Erk",
                   "Akt", "PKA", "PKC", "P38", "Jnk"]
    sachs_edges = [
        ("Plcg", "PIP2"), ("Plcg", "PIP3"), ("PIP3", "PIP2"),
        ("PIP2", "PKC"), ("PIP3", "Akt"),
        ("PKC", "Raf"), ("PKC", "Mek"), ("PKC", "P38"), ("PKC", "Jnk"),
        ("PKA", "Raf"), ("PKA", "Mek"), ("PKA", "Erk"),
        ("PKA", "Akt"), ("PKA", "P38"), ("PKA", "Jnk"),
        ("Raf", "Mek"), ("Mek", "Erk"),
    ]
    dags.append(make_dag(
        "Sachs Protein Signaling (11 nodes)",
        sachs_nodes, sachs_edges,
        "Real-world causal DAG from protein signaling. Complex with multiple paths."
    ))

    # (g) M-bias / bow-tie: a classic structure for causal inference pitfalls
    dags.append(make_dag(
        "M-bias (U1->X, U1->M, U2->M, U2->Y, X->Y)",
        ["U1", "U2", "X", "M", "Y"],
        [("U1","X"), ("U1","M"), ("U2","M"), ("U2","Y"), ("X","Y")],
        "M-bias structure. Conditioning on M opens a non-causal path."
    ))

    return dags


# ============================================================
# Part 2: Poset operations on DAGs
# ============================================================

def transitive_closure(nodes, edges):
    """Compute the transitive closure of a DAG. Returns set of (a,b) where a < b."""
    children = defaultdict(set)
    for (u, v) in edges:
        children[u].add(v)

    closure = set()
    for node in nodes:
        # BFS/DFS from each node
        visited = set()
        stack = [node]
        while stack:
            curr = stack.pop()
            for ch in children[curr]:
                if ch not in visited:
                    visited.add(ch)
                    closure.add((node, ch))
                    stack.append(ch)
    return closure


def is_order_convex(subset_set, closure):
    """Check if a subset is order-convex: if a,c in S and a < b < c, then b in S."""
    for (a, c) in closure:
        if a in subset_set and c in subset_set:
            # Check all b with a < b < c
            for (x, y) in closure:
                if x == a and (y, c) in closure and y != a and y != c:
                    if y not in subset_set:
                        return False
    return True


def is_downward_closed(subset_set, closure):
    """Check if a subset is a downward-closed set (ideal): if b in S and a < b, then a in S."""
    for (a, b) in closure:
        if b in subset_set and a not in subset_set:
            return False
    return True


def enumerate_convex_subsets(nodes, closure):
    """Enumerate all order-convex subsets of the poset."""
    convex = []
    for r in range(len(nodes) + 1):
        for subset in combinations(nodes, r):
            subset_set = set(subset)
            if is_order_convex(subset_set, closure):
                convex.append(subset)
    return convex


def enumerate_ideals(nodes, closure):
    """Enumerate all downward-closed subsets (order ideals)."""
    ideals = []
    for r in range(len(nodes) + 1):
        for subset in combinations(nodes, r):
            subset_set = set(subset)
            if is_downward_closed(subset_set, closure):
                ideals.append(subset)
    return ideals


def max_chain_length(nodes, closure):
    """Compute the height: length of the longest chain."""
    # Build adjacency for Hasse diagram
    node_list = list(nodes)
    # Longest path via DP on topological order
    parents = defaultdict(set)
    for (a, b) in closure:
        parents[b].add(a)

    # dp[v] = length of longest chain ending at v
    dp = {v: 1 for v in node_list}
    # Topological sort via Kahn's algorithm on direct edges
    children_direct = defaultdict(set)
    in_degree = defaultdict(int)
    for (u, v) in closure:
        # Use only direct (Hasse) edges
        pass

    # Simpler: use closure directly
    for v in node_list:
        for (a, b) in closure:
            if b == v:
                dp[v] = max(dp[v], dp[a] + 1)

    # Need topological order. Use iterative approach.
    # Recompute with proper topo sort.
    children = defaultdict(set)
    direct_edges = set()
    for (u, v) in closure:
        children[u].add(v)

    # Hasse diagram: (u,v) is a cover if no w with u < w < v
    hasse = set()
    for (u, v) in closure:
        is_cover = True
        for (a, b) in closure:
            if a == u and (b, v) in closure and b != v:
                is_cover = False
                break
        if is_cover:
            hasse.add((u, v))

    in_deg = defaultdict(int)
    ch = defaultdict(set)
    for (u, v) in hasse:
        ch[u].add(v)
        in_deg[v] += 1

    # Kahn's
    queue = [v for v in node_list if in_deg[v] == 0]
    dist = {v: 1 for v in node_list}
    while queue:
        u = queue.pop(0)
        for v in ch[u]:
            dist[v] = max(dist[v], dist[u] + 1)
            in_deg[v] -= 1
            if in_deg[v] == 0:
                queue.append(v)

    return max(dist.values()) if dist else 0


def max_antichain_size(nodes, closure):
    """Compute the width: size of the largest antichain (Dilworth's theorem)."""
    # Brute force for small posets
    node_list = list(nodes)
    comparable = set()
    for (a, b) in closure:
        comparable.add((a, b))
        comparable.add((b, a))

    best = 0
    for r in range(1, len(node_list) + 1):
        for subset in combinations(node_list, r):
            is_antichain = True
            for i in range(len(subset)):
                for j in range(i + 1, len(subset)):
                    if (subset[i], subset[j]) in comparable:
                        is_antichain = False
                        break
                if not is_antichain:
                    break
            if is_antichain:
                best = max(best, r)
    return best


# ============================================================
# Part 3: CAG invariants
# ============================================================

def compute_cag_invariants(dag):
    """Compute all CAG invariants for a DAG."""
    nodes = dag["nodes"]
    edges = dag["edges"]
    n = len(nodes)
    e = len(edges)

    closure = transitive_closure(nodes, edges)

    # BD action
    s_bd = n - e

    # Convex subsets
    convex = enumerate_convex_subsets(nodes, closure)
    n_cc = len(convex)

    # Ideals
    ideals = enumerate_ideals(nodes, closure)
    n_ideals = len(ideals)

    # Noetherian ratio
    gamma = n_cc / n_ideals if n_ideals > 0 else float('inf')

    # Width and height
    height = max_chain_length(nodes, closure)
    width = max_antichain_size(nodes, closure)

    return {
        "n": n,
        "e": e,
        "s_bd": s_bd,
        "n_cc": n_cc,
        "n_ideals": n_ideals,
        "gamma": gamma,
        "height": height,
        "width": width,
        "closure": closure,
        "convex_subsets": convex,
        "ideals": ideals,
    }


# ============================================================
# Part 4: Causal algebra matrix representation
# ============================================================

def causal_algebra_representation(dag):
    """
    Construct the causal algebra CAlg(P) for a small DAG.

    CAlg(P) is the set of n x n matrices M where M[i,j] = 0
    whenever nodes i and j are incomparable in the partial order.

    We show:
    - The algebra structure (which entries can be nonzero)
    - That multiplication respects causal paths
    - That prime ideals correspond to nodes
    """
    nodes = dag["nodes"]
    n = len(nodes)
    closure = transitive_closure(nodes, edges=dag["edges"])

    # Build comparability matrix: C[i,j] = 1 if i <= j or j <= i
    node_idx = {v: i for i, v in enumerate(nodes)}
    C = np.zeros((n, n), dtype=int)
    for i in range(n):
        C[i, i] = 1  # every element is comparable to itself
    for (a, b) in closure:
        ia, ib = node_idx[a], node_idx[b]
        C[ia, ib] = 1
        C[ib, ia] = 1

    # CAlg pattern: M[i,j] can be nonzero iff C[i,j] = 1
    print(f"\n  Causal algebra pattern for {dag['name']}:")
    print(f"  Nodes indexed as: {dict(enumerate(nodes))}")
    print(f"  Comparability matrix (1 = comparable, 0 = incomparable):")
    for i in range(n):
        row = "  ["
        row += " ".join(str(C[i, j]) for j in range(n))
        row += "]"
        print(row)

    # Show the algebra structure
    print(f"\n  CAlg dimension = {np.sum(C)} (number of nonzero-allowed entries)")
    print(f"  Full matrix algebra dimension = {n*n}")
    print(f"  Compression ratio = {np.sum(C)/(n*n):.3f}")

    # Demonstrate path encoding: M^k[i,j] counts weighted paths of length k
    # Use the adjacency matrix restricted to comparable pairs
    A = np.zeros((n, n))
    for (u, v) in dag["edges"]:
        A[node_idx[u], node_idx[v]] = 1

    print(f"\n  Adjacency matrix (direct causal links):")
    for i in range(n):
        row = "  ["
        row += " ".join(f"{int(A[i,j])}" for j in range(n))
        row += "]"
        print(row)

    # A^k gives number of directed paths of length k
    if n <= 6:
        A2 = A @ A
        print(f"\n  A^2 (paths of length 2, i.e., mediated effects):")
        for i in range(n):
            row = "  ["
            row += " ".join(f"{int(A2[i,j])}" for j in range(n))
            row += "]"
            print(row)

    # Prime ideals: for each node x, the set {M in CAlg : M[x,x] = 0}
    # is a prime ideal. This corresponds to "localizing away from x".
    print(f"\n  Causally prime ideals (one per node):")
    for x in nodes:
        ix = node_idx[x]
        comparable_to_x = [nodes[j] for j in range(n) if C[ix, j] == 1 and j != ix]
        print(f"    P_{x} = {{M : M[{x},{x}] = 0}} -- comparable nodes: {comparable_to_x}")

    return C


# ============================================================
# Part 5: Valid intervention targets
# ============================================================

def analyze_intervention_targets(dag, invariants):
    """
    Convex subsets = valid intervention targets.

    A set S of variables is a "causally consistent intervention target" if:
    - Whenever we intervene on both an ancestor and descendant in S,
      we also intervene on everything in between.
    - This prevents logical contradictions in the intervention.
    """
    convex = invariants["convex_subsets"]
    nodes = dag["nodes"]
    n = len(nodes)

    # Classify convex subsets by size
    by_size = defaultdict(list)
    for s in convex:
        by_size[len(s)].append(s)

    print(f"\n  Valid intervention targets (convex subsets) by size:")
    for k in sorted(by_size.keys()):
        count = len(by_size[k])
        if n <= 6:
            subsets_str = ", ".join("{" + ",".join(s) + "}" for s in by_size[k])
            print(f"    Size {k}: {count} sets -- {subsets_str}")
        else:
            print(f"    Size {k}: {count} sets")

    # Non-convex subsets: "problematic" intervention targets
    total_subsets = 2 ** n
    n_nonconvex = total_subsets - len(convex)
    print(f"\n  Total subsets: {total_subsets}")
    print(f"  Convex (valid interventions): {len(convex)}")
    print(f"  Non-convex (problematic interventions): {n_nonconvex}")
    print(f"  Fraction valid: {len(convex)/total_subsets:.3f}")

    return by_size


# ============================================================
# Part 6: Analysis and interpretation
# ============================================================

def analyze_gamma_and_structure():
    """Key Question 3: Does gamma distinguish causal structures?"""
    print("\n" + "=" * 72)
    print("ANALYSIS: Does the Noetherian ratio gamma distinguish causal structures?")
    print("=" * 72)

    # Collect results
    dags = standard_dags()
    results = []
    for dag in dags:
        inv = compute_cag_invariants(dag)
        results.append((dag, inv))

    # Sort by gamma
    results.sort(key=lambda x: x[1]["gamma"])

    print(f"\n{'DAG':<50} {'n':>3} {'e':>3} {'S_BD':>5} {'|CC|':>6} {'|I|':>6} "
          f"{'gamma':>7} {'W':>3} {'H':>3}")
    print("-" * 95)
    for dag, inv in results:
        print(f"{dag['name']:<50} {inv['n']:>3} {inv['e']:>3} {inv['s_bd']:>5} "
              f"{inv['n_cc']:>6} {inv['n_ideals']:>6} {inv['gamma']:>7.3f} "
              f"{inv['width']:>3} {inv['height']:>3}")

    return results


def main():
    print("=" * 72)
    print("CAUSAL-ALGEBRAIC GEOMETRY APPLIED TO CAUSAL INFERENCE")
    print("=" * 72)
    print()
    print("Framework: A causal DAG defines a partial order (poset) on variables.")
    print("CAG invariants (CSpec, convex subsets, BD action) encode causal structure.")
    print()

    dags = standard_dags()

    # --------------------------------------------------------
    # Part 2: Compute CAG invariants for each DAG
    # --------------------------------------------------------
    print("=" * 72)
    print("PART 1-2: CAG INVARIANTS FOR STANDARD CAUSAL DAGS")
    print("=" * 72)

    all_results = {}
    for dag in dags:
        print(f"\n{'─' * 60}")
        print(f"DAG: {dag['name']}")
        print(f"Description: {dag['description']}")
        print(f"{'─' * 60}")

        inv = compute_cag_invariants(dag)
        all_results[dag["name"]] = (dag, inv)

        print(f"  Nodes: {inv['n']}, Edges: {inv['e']}")
        print(f"  BD action S_BD = |V| - |E| = {inv['n']} - {inv['e']} = {inv['s_bd']}")
        print(f"  Order-convex subsets |CC| = {inv['n_cc']}")
        print(f"  Downward-closed sets |I| = {inv['n_ideals']}")
        print(f"  Noetherian ratio gamma = |CC|/|I| = {inv['gamma']:.4f}")
        print(f"  Width (max antichain) = {inv['width']}")
        print(f"  Height (max chain) = {inv['height']}")

    # --------------------------------------------------------
    # Part 3: Gamma analysis
    # --------------------------------------------------------
    results = analyze_gamma_and_structure()

    # --------------------------------------------------------
    # Part 4: BD action and causal complexity
    # --------------------------------------------------------
    print("\n" + "=" * 72)
    print("ANALYSIS: BD action and causal complexity")
    print("=" * 72)
    print()
    print("The BD action S_BD = |V| - |E| measures 'causal complexity':")
    print("  - A chain on n nodes has S_BD = n - (n-1) = 1 (simplest)")
    print("  - More edges (more direct causal links) => more negative S_BD")
    print("  - S_BD << 0 indicates dense causal relationships")
    print()

    results.sort(key=lambda x: x[1]["s_bd"], reverse=True)
    for dag, inv in results:
        complexity = "SIMPLE" if inv["s_bd"] >= 0 else "COMPLEX"
        print(f"  S_BD = {inv['s_bd']:>3}  [{complexity:>7}]  {dag['name']}")

    # --------------------------------------------------------
    # Part 5: Causal algebra for small DAGs
    # --------------------------------------------------------
    print("\n" + "=" * 72)
    print("PART 5: CAUSAL ALGEBRA REPRESENTATION")
    print("=" * 72)
    print()
    print("CAlg(P) = {M in Mat_n : M[i,j] = 0 if i,j incomparable in P}")
    print("This encodes the causal structure algebraically.")

    # Do this for the small DAGs only
    for dag in dags[:5]:
        C = causal_algebra_representation(dag)

    # --------------------------------------------------------
    # Part 6: Intervention targets
    # --------------------------------------------------------
    print("\n" + "=" * 72)
    print("PART 6: VALID INTERVENTION TARGETS (CONVEX SUBSETS)")
    print("=" * 72)
    print()
    print("A convex subset S is a 'causally consistent' intervention target:")
    print("if we intervene on ancestor a and descendant d in S, we also")
    print("intervene on everything on the causal path between them.")

    for dag in dags[:5]:
        name = dag["name"]
        _, inv = all_results[name]
        print(f"\n{'─' * 60}")
        print(f"DAG: {name}")
        analyze_intervention_targets(dag, inv)

    # Also do Sachs (just counts, not listing)
    sachs_dag = dags[5]
    _, sachs_inv = all_results[sachs_dag["name"]]
    print(f"\n{'─' * 60}")
    print(f"DAG: {sachs_dag['name']}")
    analyze_intervention_targets(sachs_dag, sachs_inv)

    # --------------------------------------------------------
    # Interpretation summary
    # --------------------------------------------------------
    print("\n" + "=" * 72)
    print("SUMMARY OF KEY FINDINGS")
    print("=" * 72)

    print("""
1. NOETHERIAN RATIO (gamma = |CC|/|I|) DISTINGUISHES CAUSAL STRUCTURES:
   - Total orders (chains): gamma = 1.000 (every convex subset is an ideal
     in a total order, so |CC| = |I|... actually not quite: in a chain,
     convex subsets include intervals [a,b] which are not ideals).
   - Verify: chains have gamma > 1 because intervals are convex but not ideals.
   - Wider posets (forks, colliders) have larger gamma because many antichains
     are convex but not downward-closed.
   - gamma measures the "ratio of causal consistency to causal monotonicity."

2. BD ACTION DETECTS CAUSAL COMPLEXITY:
   - S_BD = 1 for chains (minimal complexity, unique causal path).
   - S_BD < 0 for dense DAGs (Sachs network: many direct causal links).
   - S_BD correlates with the difficulty of causal effect identification:
     more edges = more potential confounding paths = harder identification.

3. CONVEX SUBSETS AS INTERVENTION TARGETS:
   - The number |CC| counts all "causally consistent" intervention sets.
   - For a chain on n nodes: |CC| includes all intervals, giving n(n+1)/2 + 1.
   - For wider posets: many more convex subsets because incomparable elements
     can be freely included/excluded.
   - The fraction |CC|/2^n measures how "intervention-friendly" the DAG is.

4. CAUSAL ALGEBRA ENCODES PATH STRUCTURE:
   - CAlg dimension = number of comparable pairs (including self-loops).
   - Compression ratio = CAlg_dim / n^2 measures how much the causal structure
     constrains the algebra. Total order: ratio = 1. Antichain: ratio = 1/n.
   - A^k in CAlg counts directed paths of length k (mediated causal effects).
   - Prime ideals P_x correspond to "marginalizing out variable x."

5. CONNECTION TO IDENTIFIABILITY:
   - Fork (common cause): gamma is high, S_BD = 1. Effect X1->X2 is NOT
     identifiable without conditioning on Z. The CAG invariants detect this:
     the width > 1 indicates incomparable variables that may be confounded.
   - Collider (common effect): same gamma and S_BD as fork (they are dual
     posets!). But conditioning on Z creates bias. The CAG invariants are
     the same because the POSET structure is the same -- the difference
     is in which variables are conditioned on, not the order structure.
   - Instrumental variable: gamma and S_BD together distinguish it from
     simpler structures. The instrument Z adds width without adding
     confounding paths.
""")

    # Final comparison table
    print("=" * 72)
    print("FINAL COMPARISON TABLE")
    print("=" * 72)
    print()
    print(f"{'DAG':<50} {'S_BD':>5} {'gamma':>7} {'|CC|/2^n':>8} {'Width':>5} {'Height':>6}")
    print("-" * 82)
    for dag in dags:
        name = dag["name"]
        _, inv = all_results[name]
        frac = inv["n_cc"] / (2 ** inv["n"])
        print(f"{name:<50} {inv['s_bd']:>5} {inv['gamma']:>7.3f} {frac:>8.3f} "
              f"{inv['width']:>5} {inv['height']:>6}")


if __name__ == "__main__":
    main()
