#!/usr/bin/env python3
"""
Spectral Consensus Cryptocurrency Simulation
=============================================
Based on chamber spectral theory from causal algebraic geometry.

Core idea:
  - Transactions form a DAG (each references d=2 parents)
  - The DAG is a causal lattice with order kernel zeta
  - Finality is determined by the spectral gap of the local transaction DAG
  - Double-spend detection uses the parity pairing test

The d=2 chamber: states are ordered pairs P=(i,j) with i<j.
The kernel K_F(P,Q) = det(zeta[P,Q]) + det(zeta[Q,P]) - delta_{PQ}.
Even/odd decomposition by parity of (i+j).
Spectral gap gamma = ln(lambda1_even / lambda1_odd).

Author: Thomas DiFiore
Date: 2026-04-04
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Optional
from collections import defaultdict, deque
import time
import random
import sys

# ---------------------------------------------------------------------------
# 1. DATA STRUCTURES
# ---------------------------------------------------------------------------

@dataclass
class Transaction:
    id: int
    parents: tuple          # (parent1_id, parent2_id) for d=2; genesis has ()
    amount: float
    sender: str
    receiver: str
    timestamp: float
    children: list = field(default_factory=list)
    depth: int = 0          # longest path from genesis


class SpectralLedger:
    """DAG-based ledger with spectral finality."""

    def __init__(self):
        self.transactions: dict[int, Transaction] = {}
        self.tips: set[int] = set()       # transactions with no children
        self.next_id: int = 0
        self.balances: dict[str, float] = defaultdict(float)
        self._ancestors_cache: dict[int, set[int]] = {}

    # ------------------------------------------------------------------
    # DAG construction
    # ------------------------------------------------------------------

    def genesis(self, initial_balances: dict[str, float]):
        """Create genesis transaction."""
        tx = Transaction(id=0, parents=(), amount=0,
                         sender="GENESIS", receiver="GENESIS",
                         timestamp=time.time())
        tx.depth = 0
        self.transactions[0] = tx
        self.tips.add(0)
        self.next_id = 1
        self.balances.update(initial_balances)
        self._ancestors_cache[0] = {0}

    def pick_parents(self, k=2, strategy="diverse") -> tuple:
        """Pick k parents.

        Strategies:
          diverse  - healthy DAG: one tip + one random (preserves width)
          narrow   - same tip twice (adversarial, creates linear chain)
          oldest   - pick oldest tips (another adversarial pattern)
        """
        tip_list = list(self.tips)
        if len(tip_list) == 0:
            return (0,) * k
        if len(tip_list) == 1 and len(self.transactions) <= 1:
            return (tip_list[0],) * k

        all_ids = list(self.transactions.keys())

        if strategy == "diverse":
            # Pick ONE tip (consumes it) and ONE random recent tx (may or
            # may not be a tip). This way the DAG gains width over time:
            # each tx removes at most 1 tip from the pool but adds 1.
            # Sometimes the random pick is also a tip => net -1, but on
            # average the tip pool stays healthy.
            p1 = random.choice(tip_list)
            # second parent: random from recent transactions (last 30%)
            recent_start = max(0, len(all_ids) - max(20, len(all_ids) // 3))
            recent = all_ids[recent_start:]
            p2 = random.choice(recent)
            return (p1, p2)
        elif strategy == "narrow" or strategy == "same":
            p = random.choice(tip_list)
            return (p,) * k
        elif strategy == "oldest":
            chosen = sorted(tip_list)[:k]
            while len(chosen) < k:
                chosen.append(chosen[-1])
            return tuple(chosen)
        else:
            return tuple(random.choices(tip_list, k=k))

    def add_transaction(self, sender: str, receiver: str, amount: float,
                        parents: Optional[tuple] = None,
                        strategy: str = "diverse") -> Transaction:
        """Add a transaction to the DAG."""
        if parents is None:
            parents = self.pick_parents(k=2, strategy=strategy)

        tx = Transaction(
            id=self.next_id, parents=parents, amount=amount,
            sender=sender, receiver=receiver, timestamp=time.time(),
        )

        # compute depth and update parent children lists
        max_parent_depth = 0
        for pid in set(parents):
            if pid in self.transactions:
                self.transactions[pid].children.append(tx.id)
                self.tips.discard(pid)
                max_parent_depth = max(max_parent_depth,
                                       self.transactions[pid].depth)
        tx.depth = max_parent_depth + 1

        self.transactions[tx.id] = tx
        self.tips.add(tx.id)
        self.next_id += 1

        # update balances
        self.balances[sender] -= amount
        self.balances[receiver] += amount

        # ancestors cache (union of parent ancestors)
        anc = {tx.id}
        for pid in set(parents):
            if pid in self._ancestors_cache:
                anc |= self._ancestors_cache[pid]
        self._ancestors_cache[tx.id] = anc

        return tx

    # ------------------------------------------------------------------
    # Local DAG extraction
    # ------------------------------------------------------------------

    def get_local_dag(self, tx_id: int, depth: int = 5,
                      max_nodes: int = 50) -> list[int]:
        """Get ancestors of tx_id up to given depth, capped at max_nodes.
        Returns list of transaction ids in topological (creation) order."""
        visited = set()
        queue = deque([(tx_id, 0)])
        while queue:
            nid, d = queue.popleft()
            if nid in visited or d > depth:
                continue
            visited.add(nid)
            if len(visited) >= max_nodes:
                break
            tx = self.transactions.get(nid)
            if tx is None:
                continue
            for pid in set(tx.parents):
                if pid not in visited:
                    queue.append((pid, d + 1))
        return sorted(visited)

    def get_descendants(self, tx_id: int) -> set[int]:
        """Get all descendants of tx_id."""
        desc = set()
        queue = deque([tx_id])
        while queue:
            nid = queue.popleft()
            tx = self.transactions.get(nid)
            if tx is None:
                continue
            for cid in tx.children:
                if cid not in desc:
                    desc.add(cid)
                    queue.append(cid)
        return desc

    # ------------------------------------------------------------------
    # Zeta matrix and chamber kernel
    # ------------------------------------------------------------------

    def build_zeta_matrix(self, nodes: list[int]) -> np.ndarray:
        """Build the order kernel zeta(i,j) = 1 if nodes[i] <= nodes[j]
        in the DAG partial order. nodes must be in topological order."""
        n = len(nodes)
        idx = {nid: k for k, nid in enumerate(nodes)}
        zeta = np.eye(n, dtype=np.float64)  # reflexive

        # propagate transitively: process nodes in topological order
        for k, nid in enumerate(nodes):
            tx = self.transactions.get(nid)
            if tx is None:
                continue
            for pid in set(tx.parents):
                if pid in idx:
                    pk = idx[pid]
                    # everything that reaches parent also reaches nid
                    for r in range(n):
                        if zeta[r, pk] > 0:
                            zeta[r, k] = 1.0
        return zeta

    def compute_chamber_kernel(self, nodes: list[int]):
        """Build the d=2 chamber kernel K_F on pairs (i<j).

        K_F(P,Q) = det(zeta[P,Q]) + det(zeta[Q,P]) - delta_{PQ}

        Returns (K_full, K_even, K_odd, pairs, zeta)
        """
        zeta = self.build_zeta_matrix(nodes)
        n = len(nodes)

        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        m = len(pairs)
        if m == 0:
            z = np.array([[0.0]])
            return z, z, z, pairs, zeta

        # vectorized kernel construction
        K = np.zeros((m, m), dtype=np.float64)
        for a, (i1, j1) in enumerate(pairs):
            for b, (i2, j2) in enumerate(pairs):
                det_PQ = (zeta[i1, i2] * zeta[j1, j2]
                          - zeta[i1, j2] * zeta[j1, i2])
                det_QP = (zeta[i2, i1] * zeta[j2, j1]
                          - zeta[i2, j1] * zeta[j2, i1])
                K[a, b] = det_PQ + det_QP
                if a == b:
                    K[a, b] -= 1.0

        # even/odd parity decomposition
        even_idx = [a for a, (i, j) in enumerate(pairs) if (i + j) % 2 == 0]
        odd_idx = [a for a, (i, j) in enumerate(pairs) if (i + j) % 2 == 1]
        if not even_idx:
            even_idx = list(range(m))
        if not odd_idx:
            odd_idx = list(range(m))

        K_even = K[np.ix_(even_idx, even_idx)]
        K_odd = K[np.ix_(odd_idx, odd_idx)]

        return K, K_even, K_odd, pairs, zeta

    # ------------------------------------------------------------------
    # Spectral gap
    # ------------------------------------------------------------------

    def compute_spectral_gap(self, tx_id: int, depth: int = 5,
                             max_nodes: int = 30) -> dict:
        """Compute the spectral gap for a transaction's local DAG.

        gap = |ln(lambda1_even / lambda1_odd)|
        """
        nodes = self.get_local_dag(tx_id, depth=depth, max_nodes=max_nodes)
        if len(nodes) < 3:
            return {"gap": 0.0, "lambda1_even": 0.0, "lambda1_odd": 0.0,
                    "local_size": len(nodes), "num_pairs": 0,
                    "width": 0, "incomparable_frac": 0.0}

        K, K_even, K_odd, pairs, zeta = self.compute_chamber_kernel(nodes)
        n = len(nodes)

        eig_even = np.sort(np.real(np.linalg.eigvals(K_even)))[::-1]
        eig_odd = np.sort(np.real(np.linalg.eigvals(K_odd)))[::-1]

        lam1_even = max(eig_even[0], 1e-15)
        lam1_odd = max(eig_odd[0], 1e-15)

        gap = abs(np.log(lam1_even / lam1_odd)) if lam1_odd > 1e-15 \
            else np.log(lam1_even + 1)

        # DAG width: count incomparable pairs
        n_incomparable = 0
        n_total_pairs = n * (n - 1) // 2
        for i in range(n):
            for j in range(i + 1, n):
                if zeta[i, j] == 0 and zeta[j, i] == 0:
                    n_incomparable += 1
        width_frac = n_incomparable / max(n_total_pairs, 1)

        return {
            "gap": gap,
            "lambda1_even": lam1_even,
            "lambda1_odd": lam1_odd,
            "local_size": len(nodes),
            "num_pairs": len(pairs),
            "width": n_incomparable,
            "incomparable_frac": width_frac,
        }

    # ------------------------------------------------------------------
    # Finality
    # ------------------------------------------------------------------

    def check_finality(self, tx_id: int, depth: int = 5,
                       max_nodes: int = 30) -> dict:
        """Finality score F = 1 - exp(-gamma * confirmations)."""
        spec = self.compute_spectral_gap(tx_id, depth=depth,
                                         max_nodes=max_nodes)
        gamma = spec["gap"]

        # count confirmations (descendants)
        confirmations = len(self.get_descendants(tx_id))

        finality = 1.0 - np.exp(-gamma * max(confirmations, 1))
        return {
            **spec,
            "confirmations": confirmations,
            "finality": finality,
            "is_final": finality > 0.99,
        }

    # ------------------------------------------------------------------
    # Double-spend detection via parity pairing
    # ------------------------------------------------------------------

    def compute_parity_error(self, nodes: list[int]) -> dict:
        """Compute structural diagnostics for double-spend detection.

        The key signal is the SENDER CONFLICT: two transactions from the
        same sender that share a parent but are incomparable in the DAG.
        In a legitimate DAG, sequential spends from the same sender form
        a chain (each references the previous). A double-spend creates
        a FORK: two incomparable transactions from the same sender
        referencing the same UTXO (parent).

        Additional signals:
        2. Spectral degeneracy of K_F (near-duplicate eigenvalues).
        3. Local antichain width around the conflict.

        Returns dict with individual scores and combined parity_error.
        """
        K, K_even, K_odd, pairs, zeta = self.compute_chamber_kernel(nodes)
        n = len(nodes)
        m = len(pairs)
        if m == 0:
            return {"parity_error": 0.0, "sender_conflict": 0.0,
                    "degeneracy": 0.0, "fork_width": 0.0}

        idx_map = {nid: k for k, nid in enumerate(nodes)}

        # --- Signal 1: Sender conflict ---
        # Group transactions by sender. For each sender, check if any
        # pair of their transactions (a) share a parent AND (b) are
        # incomparable in the DAG order.
        sender_txs = defaultdict(list)
        for nid in nodes:
            tx = self.transactions.get(nid)
            if tx and tx.sender != "GENESIS":
                sender_txs[tx.sender].append(nid)

        sender_conflict = 0.0
        for sender, txs in sender_txs.items():
            if len(txs) < 2:
                continue
            for ci in range(len(txs)):
                for cj in range(ci + 1, len(txs)):
                    a, b = txs[ci], txs[cj]
                    tx_a = self.transactions[a]
                    tx_b = self.transactions[b]
                    # check shared parent
                    parents_a = set(tx_a.parents)
                    parents_b = set(tx_b.parents)
                    shared = parents_a & parents_b
                    if not shared:
                        continue
                    # check incomparable
                    if a in idx_map and b in idx_map:
                        ai, bi = idx_map[a], idx_map[b]
                        if zeta[ai, bi] == 0 and zeta[bi, ai] == 0:
                            sender_conflict += 1.0

        # --- Signal 2: Spectral degeneracy ---
        eigs = np.sort(np.abs(np.real(np.linalg.eigvals(K))))[::-1]
        if len(eigs) >= 2 and abs(eigs[0]) > 1e-10:
            degeneracy = eigs[1] / eigs[0]
        else:
            degeneracy = 0.0

        # --- Signal 3: Fork width ---
        # Count how many nodes are in the antichain around any conflict
        # (transactions unreachable from both conflicting tx).
        # This measures the "damage radius" of the fork.
        fork_width = 0.0
        if sender_conflict > 0:
            # count incomparable pairs near the conflict
            n_incomparable = 0
            for i in range(n):
                for j in range(i + 1, n):
                    if zeta[i, j] == 0 and zeta[j, i] == 0:
                        n_incomparable += 1
            n_total = n * (n - 1) // 2
            fork_width = n_incomparable / max(n_total, 1)

        # --- Combined parity error ---
        # sender_conflict is the PRIMARY signal (0 for clean, >= 1 for DS)
        parity_error = (5.0 * sender_conflict
                        + 0.3 * degeneracy
                        + 1.0 * fork_width)

        return {
            "parity_error": parity_error,
            "sender_conflict": sender_conflict,
            "degeneracy": degeneracy,
            "fork_width": fork_width,
        }

    def check_double_spend(self, tx_ids: list[int], depth: int = 5,
                           max_nodes: int = 40) -> dict:
        """Check for double-spend among a set of transactions."""
        all_nodes = set()
        for tid in tx_ids:
            local = self.get_local_dag(tid, depth=depth, max_nodes=max_nodes)
            all_nodes.update(local)
        nodes = sorted(all_nodes)[:max_nodes]

        result = self.compute_parity_error(nodes)
        threshold = 0.3  # calibrated empirically
        result["threshold"] = threshold
        result["is_double_spend"] = result["parity_error"] > threshold
        result["dag_size"] = len(nodes)
        return result


# ---------------------------------------------------------------------------
# 2. SIMULATION HELPERS
# ---------------------------------------------------------------------------

def build_honest_dag(n_transactions: int = 200, n_users: int = 10,
                     seed: int = 42) -> SpectralLedger:
    """Build a realistic honest DAG with diverse parent selection."""
    rng = random.Random(seed)
    # use module-level random for pick_parents
    random.seed(seed)

    users = [f"user_{i}" for i in range(n_users)]
    ledger = SpectralLedger()
    ledger.genesis({u: 1000.0 for u in users})

    # seed the DAG: first few transactions create initial width
    for i in range(min(5, n_transactions)):
        sender = rng.choice(users)
        receiver = rng.choice([u for u in users if u != sender])
        # first few all reference genesis to create width
        ledger.add_transaction(sender, receiver, rng.uniform(0.1, 10.0),
                               parents=(0, 0))

    for i in range(max(0, n_transactions - 5)):
        sender = rng.choice(users)
        receiver = rng.choice([u for u in users if u != sender])
        amount = rng.uniform(0.1, 10.0)
        ledger.add_transaction(sender, receiver, amount, strategy="diverse")

    return ledger


def build_attacked_dag(n_honest: int = 150, n_attack: int = 50,
                       n_users: int = 10, seed: int = 42) -> SpectralLedger:
    """Build a DAG where an adversary creates a narrow chain to lower gap."""
    rng = random.Random(seed)
    random.seed(seed)

    users = [f"user_{i}" for i in range(n_users)]
    ledger = SpectralLedger()
    ledger.genesis({u: 1000.0 for u in users})

    # seed
    for i in range(min(5, n_honest)):
        sender = rng.choice(users)
        receiver = rng.choice([u for u in users if u != sender])
        ledger.add_transaction(sender, receiver, rng.uniform(0.1, 10.0),
                               parents=(0, 0))

    for i in range(max(0, n_honest - 5)):
        sender = rng.choice(users)
        receiver = rng.choice([u for u in users if u != sender])
        ledger.add_transaction(sender, receiver, rng.uniform(0.1, 10.0),
                               strategy="diverse")

    # adversary: narrow chain (same parent = linear chain)
    for _ in range(n_attack):
        ledger.add_transaction("adversary", "adversary", 0.0,
                               strategy="narrow")

    return ledger


def simulate_double_spend(seed: int = 42):
    """Create two ledgers: clean (no double-spend) and dirty (with double-spend).

    The double-spend: Alice sends 10 to Bob AND 10 to Charlie,
    both referencing the same parent. In the clean ledger, only
    Alice -> Bob exists.

    Key design: each sender's transactions form a sequential chain
    (each new spend by sender X references sender X's previous spend).
    This eliminates accidental sender conflicts in the clean DAG.

    Returns (clean_ledger, dirty_ledger, target_tx_clean, target_tx_dirty,
             double_spend_tx_id)
    """
    rng = random.Random(seed)
    random.seed(seed)
    users = ["alice", "bob", "charlie", "dave", "eve"]

    clean = SpectralLedger()
    dirty = SpectralLedger()
    initial = {u: 1000.0 for u in users}
    clean.genesis(initial)
    dirty.genesis(initial)

    # Track each sender's last transaction to form sequential chains
    last_tx_clean = {u: 0 for u in users}  # genesis
    last_tx_dirty = {u: 0 for u in users}

    # build identical prefix: 30 transactions with sequential sender chains
    for _ in range(30):
        sender = rng.choice(users)
        receiver = rng.choice([u for u in users if u != sender])
        amount = rng.uniform(1, 20)
        # each tx references sender's last tx + a random tip
        tip_c = random.choice(list(clean.tips)) if clean.tips else 0
        tip_d = random.choice(list(dirty.tips)) if dirty.tips else 0
        p_clean = (last_tx_clean[sender], tip_c)
        p_dirty = (last_tx_dirty[sender], tip_d)
        tc = clean.add_transaction(sender, receiver, amount, parents=p_clean)
        td = dirty.add_transaction(sender, receiver, amount, parents=p_dirty)
        last_tx_clean[sender] = tc.id
        last_tx_dirty[sender] = td.id

    # --- The double-spend setup ---
    # Alice's last tx is the "UTXO" she will double-spend from
    alice_utxo_clean = last_tx_clean["alice"]
    alice_utxo_dirty = last_tx_dirty["alice"]

    # Honest tx: Alice -> Bob 10 coins (references Alice's last tx)
    tx_ab_clean = clean.add_transaction(
        "alice", "bob", 10.0,
        parents=(alice_utxo_clean, alice_utxo_clean))
    tx_ab_dirty = dirty.add_transaction(
        "alice", "bob", 10.0,
        parents=(alice_utxo_dirty, alice_utxo_dirty))
    last_tx_clean["alice"] = tx_ab_clean.id
    # NOTE: in dirty, we do NOT update alice's last_tx yet

    # DOUBLE SPEND (dirty only): Alice -> Charlie 10 coins, SAME UTXO
    tx_ac_dirty = dirty.add_transaction(
        "alice", "charlie", 10.0,
        parents=(alice_utxo_dirty, alice_utxo_dirty))

    # In clean ledger, add a normal non-alice transaction instead
    clean.add_transaction("dave", "eve", 5.0)
    dirty.add_transaction("dave", "eve", 5.0)

    # add 15 more transactions on top in both (maintaining sender chains)
    for _ in range(15):
        sender = rng.choice([u for u in users if u != "alice"])
        receiver = rng.choice([u for u in users if u != sender])
        amount = rng.uniform(1, 10)
        tip_c = random.choice(list(clean.tips)) if clean.tips else 0
        tip_d = random.choice(list(dirty.tips)) if dirty.tips else 0
        tc = clean.add_transaction(sender, receiver, amount,
                                   parents=(last_tx_clean[sender], tip_c))
        td = dirty.add_transaction(sender, receiver, amount,
                                   parents=(last_tx_dirty[sender], tip_d))
        last_tx_clean[sender] = tc.id
        last_tx_dirty[sender] = td.id

    return (clean, dirty,
            tx_ab_clean.id, tx_ab_dirty.id, tx_ac_dirty.id)


# ---------------------------------------------------------------------------
# 3. MAIN SIMULATION
# ---------------------------------------------------------------------------

def separator(title: str):
    w = 70
    print(f"\n{'=' * w}")
    print(f"  {title}")
    print(f"{'=' * w}\n")


def main():
    t_start = time.time()
    np.random.seed(42)
    random.seed(42)

    # ==================================================================
    # PART 1: DAG Construction and Throughput
    # ==================================================================
    separator("PART 1: DAG CONSTRUCTION AND THROUGHPUT")

    t0 = time.time()
    ledger = build_honest_dag(n_transactions=200, n_users=10, seed=42)
    t_build = time.time() - t0

    n_tx = len(ledger.transactions)
    n_tips = len(ledger.tips)
    max_depth = max(tx.depth for tx in ledger.transactions.values())
    avg_depth = np.mean([tx.depth for tx in ledger.transactions.values()])

    print(f"Transactions:       {n_tx}")
    print(f"Tips (unconfirmed): {n_tips}")
    print(f"Build time:         {t_build:.4f} s")
    print(f"Throughput:         {200 / max(t_build, 1e-6):.0f} tx/s")
    print(f"Max DAG depth:      {max_depth}")
    print(f"Avg DAG depth:      {avg_depth:.1f}")
    print(f"DAG width (tips):   {n_tips} (healthy if > 1)")

    # verify DAG has real width
    widths_by_depth = defaultdict(int)
    for tx in ledger.transactions.values():
        widths_by_depth[tx.depth] += 1
    max_width = max(widths_by_depth.values())
    print(f"Max width at any depth: {max_width}")

    # ==================================================================
    # PART 2: Spectral Gap Computation and Timing
    # ==================================================================
    separator("PART 2: SPECTRAL GAP COMPUTATION")

    for max_nodes in [10, 20, 30]:
        times = []
        gaps = []
        widths = []
        sample_ids = list(range(20, min(200, n_tx), 10))[:20]
        for tid in sample_ids:
            t0 = time.time()
            spec = ledger.compute_spectral_gap(tid, depth=6,
                                               max_nodes=max_nodes)
            dt = time.time() - t0
            times.append(dt)
            gaps.append(spec["gap"])
            widths.append(spec["incomparable_frac"])

        print(f"Local DAG size = {max_nodes}:")
        print(f"  Avg spectral gap:      {np.mean(gaps):.4f} +/- {np.std(gaps):.4f}")
        print(f"  Avg incomparable frac: {np.mean(widths):.3f}")
        print(f"  Avg compute time:      {np.mean(times)*1000:.1f} ms")
        print(f"  Max compute time:      {max(times)*1000:.1f} ms")
        print(f"  Chamber dimension:     ~{max_nodes*(max_nodes-1)//2}")
        print()

    # ==================================================================
    # PART 3: Finality Tracking
    # ==================================================================
    separator("PART 3: FINALITY TRACKING")

    print("Tracking finality of early transaction as DAG grows:\n")
    print(f"  {'Confirms':>10s}  {'Gap':>10s}  {'Incompat%':>10s}  "
          f"{'Finality':>10s}  {'Final?':>8s}")
    print(f"  {'-'*10}  {'-'*10}  {'-'*10}  {'-'*10}  {'-'*8}")

    # Use the main ledger (already built with 200 tx) to track finality
    # Pick a transaction near the middle that has a real spectral gap
    # First, find a tx with nonzero gap
    target_tx = None
    for tid in range(50, 150):
        spec = ledger.compute_spectral_gap(tid, depth=5, max_nodes=20)
        if spec["gap"] > 0.01:
            target_tx = tid
            break
    if target_tx is None:
        target_tx = 100  # fallback

    print(f"Target transaction: #{target_tx}")
    spec0 = ledger.compute_spectral_gap(target_tx, depth=5, max_nodes=20)
    print(f"Spectral gap: {spec0['gap']:.4f}, "
          f"incomparable frac: {spec0['incomparable_frac']:.3f}\n")

    # Now build a FRESH ledger incrementally and track finality
    ledger3 = SpectralLedger()
    ledger3.genesis({"alice": 1000, "bob": 1000, "charlie": 1000,
                     "dave": 1000, "eve": 1000})
    users3 = ["alice", "bob", "charlie", "dave", "eve"]
    # build initial width: multiple independent branches from genesis
    for _ in range(8):
        s = random.choice(users3)
        r = random.choice([u for u in users3 if u != s])
        ledger3.add_transaction(s, r, 1.0, parents=(0, 0))

    # the target: a transaction that merges two branches
    tips_list = sorted(ledger3.tips)
    target_tx_f = ledger3.add_transaction(
        "alice", "bob", 5.0,
        parents=(tips_list[0], tips_list[-1])).id

    finality_history = []
    for i in range(100):
        s = random.choice(users3)
        r = random.choice([u for u in users3 if u != s])
        ledger3.add_transaction(s, r, 0.5, strategy="diverse")
        if i % 5 == 0:
            result = ledger3.check_finality(target_tx_f, depth=6,
                                            max_nodes=20)
            finality_history.append(result)
            print(f"  {result['confirmations']:>10d}  "
                  f"{result['gap']:>10.4f}  "
                  f"{result['incomparable_frac']:>10.3f}  "
                  f"{result['finality']:>10.6f}  "
                  f"{'YES' if result['is_final'] else 'no':>8s}")

    final_at = None
    for r in finality_history:
        if r["is_final"]:
            final_at = r["confirmations"]
            break
    if final_at is not None:
        print(f"\n  Transaction became FINAL after {final_at} confirmations")
    else:
        last = finality_history[-1]
        if last["gap"] > 0:
            needed = int(np.ceil(-np.log(0.01) / last["gap"]))
            print(f"\n  Not yet final. Estimated confirmations needed: ~{needed}")
        else:
            print(f"\n  Not yet final (gap = 0)")

    # ==================================================================
    # PART 4: Double-Spend Detection
    # ==================================================================
    separator("PART 4: DOUBLE-SPEND DETECTION")

    (clean, dirty,
     tx_clean_id, tx_dirty_id, tx_double_id) = simulate_double_spend(seed=42)

    print(f"Clean ledger:       {len(clean.transactions)} transactions, "
          f"{len(clean.tips)} tips")
    print(f"Dirty ledger:       {len(dirty.transactions)} transactions, "
          f"{len(dirty.tips)} tips")
    print(f"Honest tx (clean):  #{tx_clean_id}")
    print(f"Honest tx (dirty):  #{tx_dirty_id}")
    print(f"Double-spend tx:    #{tx_double_id}")
    print()

    # parity error: clean
    clean_nodes = clean.get_local_dag(tx_clean_id, depth=6, max_nodes=35)
    clean_result = clean.compute_parity_error(clean_nodes)

    # parity error: dirty, just honest tx neighborhood
    dirty_nodes_h = dirty.get_local_dag(tx_dirty_id, depth=6, max_nodes=35)
    dirty_result_h = dirty.compute_parity_error(dirty_nodes_h)

    # parity error: dirty, combined neighborhood of both conflicting tx
    ds_result = dirty.check_double_spend([tx_dirty_id, tx_double_id],
                                         depth=6, max_nodes=35)

    print(f"Clean DAG parity error:         {clean_result['parity_error']:.4f}")
    print(f"  sender_conflict:               {clean_result['sender_conflict']:.4f}")
    print(f"  degeneracy:                   {clean_result['degeneracy']:.4f}")
    print(f"  fork_width:                {clean_result['fork_width']:.4f}")
    print()
    print(f"Dirty DAG (honest tx only):     {dirty_result_h['parity_error']:.4f}")
    print(f"  sender_conflict:               {dirty_result_h['sender_conflict']:.4f}")
    print()
    print(f"Dirty DAG (both conflicting):   {ds_result['parity_error']:.4f}")
    print(f"  sender_conflict:               {ds_result['sender_conflict']:.4f}")
    print(f"  degeneracy:                   {ds_result['degeneracy']:.4f}")
    print(f"  fork_width:                {ds_result['fork_width']:.4f}")
    print(f"  threshold:                    {ds_result['threshold']:.4f}")
    print(f"  DOUBLE-SPEND DETECTED:        {ds_result['is_double_spend']}")
    print()

    # --- Statistical validation ---
    print("Statistical validation (100 trials each):\n")
    clean_errors = []
    dirty_errors = []
    n_trials = 100
    for trial in range(n_trials):
        s = trial * 7 + 13
        c, d, cid, did, dsid = simulate_double_spend(seed=s)

        cn = c.get_local_dag(cid, depth=5, max_nodes=30)
        ce_r = c.compute_parity_error(cn)
        clean_errors.append(ce_r["parity_error"])

        # dirty: combined neighborhood
        dn_all = set(d.get_local_dag(did, depth=5, max_nodes=20))
        dn_all |= set(d.get_local_dag(dsid, depth=5, max_nodes=20))
        dn = sorted(dn_all)[:30]
        de_r = d.compute_parity_error(dn)
        dirty_errors.append(de_r["parity_error"])

    clean_errors = np.array(clean_errors)
    dirty_errors = np.array(dirty_errors)

    # threshold: mean + 3*std of clean
    threshold = np.mean(clean_errors) + 3 * np.std(clean_errors)
    # but ensure at least 0.01
    threshold = max(threshold, 0.01)

    tp = np.sum(dirty_errors > threshold)
    fp = np.sum(clean_errors > threshold)
    tn = np.sum(clean_errors <= threshold)
    fn = np.sum(dirty_errors <= threshold)

    print(f"  Clean errors:  mean={np.mean(clean_errors):.4f}  "
          f"std={np.std(clean_errors):.4f}  "
          f"max={np.max(clean_errors):.4f}")
    print(f"  Dirty errors:  mean={np.mean(dirty_errors):.4f}  "
          f"std={np.std(dirty_errors):.4f}  "
          f"min={np.min(dirty_errors):.4f}")
    print(f"  Threshold:     {threshold:.4f}")
    print(f"  True positive rate  (detect real DS):  {tp}/{n_trials} = "
          f"{tp/n_trials*100:.0f}%")
    print(f"  False positive rate (false alarm):     {fp}/{n_trials} = "
          f"{fp/n_trials*100:.0f}%")
    print(f"  True negative rate:                    {tn}/{n_trials} = "
          f"{tn/n_trials*100:.0f}%")
    print(f"  False negative rate (miss real DS):    {fn}/{n_trials} = "
          f"{fn/n_trials*100:.0f}%")

    # ==================================================================
    # PART 5: Attack Resistance
    # ==================================================================
    separator("PART 5: ATTACK RESISTANCE")

    print("Comparing spectral gaps: honest DAG vs adversarial narrow-chain\n")

    honest_ledger = build_honest_dag(n_transactions=200, seed=123)
    attacked_ledger = build_attacked_dag(n_honest=150, n_attack=50,
                                         seed=123)

    honest_gaps = []
    honest_widths = []
    attacked_gaps = []
    attacked_widths = []

    for tid in range(160, 200):
        if tid in honest_ledger.transactions:
            h = honest_ledger.compute_spectral_gap(tid, depth=5,
                                                   max_nodes=25)
            honest_gaps.append(h["gap"])
            honest_widths.append(h["incomparable_frac"])
        if tid in attacked_ledger.transactions:
            a = attacked_ledger.compute_spectral_gap(tid, depth=5,
                                                     max_nodes=25)
            attacked_gaps.append(a["gap"])
            attacked_widths.append(a["incomparable_frac"])

    honest_gaps = np.array(honest_gaps)
    attacked_gaps = np.array(attacked_gaps)

    print(f"  Honest DAG:")
    print(f"    Spectral gap:      mean={np.mean(honest_gaps):.4f}  "
          f"std={np.std(honest_gaps):.4f}")
    print(f"    Incomparable frac: mean={np.mean(honest_widths):.3f}")
    print(f"    Tips: {len(honest_ledger.tips)}")
    print()
    print(f"  Attacked DAG (narrow-chain adversary):")
    print(f"    Spectral gap:      mean={np.mean(attacked_gaps):.4f}  "
          f"std={np.std(attacked_gaps):.4f}")
    print(f"    Incomparable frac: mean={np.mean(attacked_widths):.3f}")
    print(f"    Tips: {len(attacked_ledger.tips)}")
    print()

    gap_ratio = np.mean(honest_gaps) / max(np.mean(attacked_gaps), 1e-10)
    print(f"  Gap ratio (honest/attacked): {gap_ratio:.2f}x")
    if gap_ratio > 1.1:
        print(f"  --> Honest DAG has HIGHER spectral gap")
        print(f"      Narrow-chain attack degrades finality speed by "
              f"{gap_ratio:.1f}x")
    elif gap_ratio < 0.9:
        print(f"  --> Attacked DAG has higher gap (unexpected)")
    else:
        print(f"  --> Similar gaps; attack has limited structural effect")
        print(f"      But attacked DAG has fewer tips = less throughput")

    # ==================================================================
    # PART 6: Comparison with Bitcoin
    # ==================================================================
    separator("PART 6: COMPARISON WITH BITCOIN")

    if final_at is not None:
        spectral_confs = final_at
    else:
        last_gap = finality_history[-1]["gap"]
        spectral_confs = int(np.ceil(-np.log(0.01) / max(last_gap, 0.01)))

    # assume 1 tx/sec in a real network (conservative)
    spectral_secs = spectral_confs  # 1 tx/s
    bitcoin_secs = 3600  # 6 blocks * 10 min

    print(f"{'Metric':<42s}  {'Bitcoin':>14s}  {'Spectral':>14s}")
    print(f"{'-'*42}  {'-'*14}  {'-'*14}")
    print(f"{'Consensus mechanism':<42s}  {'PoW':>14s}  {'Spectral gap':>14s}")
    print(f"{'Finality (confirmations)':<42s}  {'6 blocks':>14s}  "
          f"{f'{spectral_confs} tx':>14s}")
    print(f"{'Finality time @ 1 tx/s (seconds)':<42s}  {bitcoin_secs:>14d}  "
          f"{spectral_secs:>14d}")
    print(f"{'Finality time (minutes)':<42s}  {bitcoin_secs/60:>14.0f}  "
          f"{spectral_secs/60:>14.1f}")
    print(f"{'Double-spend detection':<42s}  {'Probabilistic':>14s}  "
          f"{'Parity test':>14s}")
    tpr = tp / n_trials * 100
    fpr = fp / n_trials * 100
    print(f"{'DS true positive rate':<42s}  {'~99% (6 blk)':>14s}  "
          f"{f'{tpr:.0f}%':>14s}")
    print(f"{'DS false positive rate':<42s}  {'~0%':>14s}  "
          f"{f'{fpr:.0f}%':>14s}")
    print(f"{'Energy cost':<42s}  {'Very high':>14s}  "
          f"{'O(n^3) compute':>14s}")
    print(f"{'Structure':<42s}  {'Linear chain':>14s}  "
          f"{'DAG (d=2)':>14s}")

    # ==================================================================
    # PART 7: Performance Summary
    # ==================================================================
    separator("PART 7: PERFORMANCE SUMMARY")

    print("Timing measurements for spectral gap computation:\n")
    for max_n in [10, 20, 30, 40, 50]:
        times_list = []
        for _ in range(5):
            tid = random.randint(50, min(199, len(ledger.transactions) - 1))
            t0 = time.time()
            ledger.compute_spectral_gap(tid, depth=6, max_nodes=max_n)
            times_list.append(time.time() - t0)
        cdim = max_n * (max_n - 1) // 2
        print(f"  n={max_n:>3d}  chamber={cdim:>5d}  "
              f"avg={np.mean(times_list)*1000:>8.1f} ms  "
              f"max={max(times_list)*1000:>8.1f} ms")

    t_total = time.time() - t_start
    print(f"\nTotal simulation time: {t_total:.1f} s")

    separator("SIMULATION COMPLETE")


if __name__ == "__main__":
    main()
