"""
lib/Holroyd_Talbot/graph_utils.py – HT-specific graph helpers for Searcher.

Import in a Holroyd-Talbot Searcher script with:
    import sys; sys.path.insert(0, '.')
    from lib.Holroyd_Talbot.graph_utils import (
        mu,
        independent_sets_of_size,
        max_intersecting_family_size,
        star_size,
    )

All functions work on networkx Graph objects.
"""

from __future__ import annotations

from itertools import combinations
from typing import List, Set, Tuple

try:
    import networkx as nx
except ImportError:  # pragma: no cover
    nx = None  # type: ignore


# ── Independent set helpers ──────────────────────────────────────────────────

def independent_sets_of_size(G: "nx.Graph", r: int) -> List[Tuple]:
    """Return all independent r-sets of G as a sorted list of tuples."""
    return [
        s for s in combinations(sorted(G.nodes()), r)
        if G.subgraph(s).number_of_edges() == 0
    ]


def star_size(v, indep_sets: List[Tuple]) -> int:
    """Number of sets in indep_sets that contain vertex v."""
    return sum(1 for s in indep_sets if v in s)


def max_star_size(G: "nx.Graph", indep_sets: List[Tuple]) -> Tuple[int, object]:
    """Return (max_star_size, star_centre) over all vertices of G."""
    best_v, best_sz = None, 0
    for v in G.nodes():
        sz = star_size(v, indep_sets)
        if sz > best_sz:
            best_sz, best_v = sz, v
    return best_sz, best_v


# ── Minimum maximal independent set (μ) ─────────────────────────────────────

def mu(G: "nx.Graph") -> int:
    """
    Compute μ(G) = size of the smallest maximal independent set of G.

    Brute-force over all subsets in increasing order of size.
    Feasible for |V(G)| ≤ ~20.
    """
    nodes = list(G.nodes())
    n = len(nodes)
    for size in range(1, n + 1):
        for S in combinations(nodes, size):
            S_set = set(S)
            # Independence check
            if any(G.has_edge(u, v) for u, v in combinations(S_set, 2)):
                continue
            # Maximality check: every vertex outside S is adjacent to some vertex in S
            if all(
                v in S_set or any(G.has_edge(v, s) for s in S_set)
                for v in nodes
            ):
                return size
    return n  # fallback (should not happen for connected non-empty G)


def mu_witness(G: "nx.Graph") -> Tuple[int, List]:
    """Return (μ(G), witness_set) — the smallest maximal independent set."""
    nodes = list(G.nodes())
    n = len(nodes)
    for size in range(1, n + 1):
        for S in combinations(nodes, size):
            S_set = set(S)
            if any(G.has_edge(u, v) for u, v in combinations(S_set, 2)):
                continue
            if all(
                v in S_set or any(G.has_edge(v, s) for s in S_set)
                for v in nodes
            ):
                return size, list(S_set)
    return n, nodes


# ── Maximum intersecting family (Bron–Kerbosch on intersection graph) ────────

def max_intersecting_family_size(indep_sets: List[Tuple]) -> int:
    """
    Return the size of the largest intersecting sub-family of indep_sets.

    Algorithm: build the intersection graph (two sets are adjacent iff they
    share at least one element), then find the maximum clique via
    Bron–Kerbosch with pivoting.

    Feasible for |indep_sets| ≤ ~300.  For larger families consider using
    max_intersecting_family_size_nx() which delegates to networkx.
    """
    n = len(indep_sets)
    if n == 0:
        return 0
    sets: List[Set] = [set(s) for s in indep_sets]

    # Adjacency matrix (bool) — i adj j iff i≠j and sets overlap
    adj: List[List[bool]] = [
        [i != j and bool(sets[i] & sets[j]) for j in range(n)]
        for i in range(n)
    ]

    best: List[int] = [0]

    def bk(R: Set[int], P: Set[int], X: Set[int]) -> None:
        if not P and not X:
            if len(R) > best[0]:
                best[0] = len(R)
            return
        # Pivot: choose vertex in P∪X with most neighbours in P
        pivot = max(P | X, key=lambda v: sum(1 for w in P if adj[v][w]))
        for v in [w for w in P if not adj[pivot][w]]:
            neighbors_v = {w for w in range(n) if adj[v][w]}
            bk(R | {v}, P & neighbors_v, X & neighbors_v)
            P = P - {v}
            X = X | {v}

    bk(set(), set(range(n)), set())
    return best[0]


def max_intersecting_family_size_nx(indep_sets: List[Tuple]) -> int:
    """
    Variant that uses networkx's max_clique when available.
    Falls back to max_intersecting_family_size for small inputs.
    """
    if nx is None:
        return max_intersecting_family_size(indep_sets)
    if len(indep_sets) <= 300:
        return max_intersecting_family_size(indep_sets)
    sets = [set(s) for s in indep_sets]
    IG = nx.Graph()
    IG.add_nodes_from(range(len(sets)))
    for i in range(len(sets)):
        for j in range(i + 1, len(sets)):
            if sets[i] & sets[j]:
                IG.add_edge(i, j)
    clique, _ = nx.max_weight_clique(IG, weight=None)
    return len(clique)


# ── HT verification ──────────────────────────────────────────────────────────

def verify_ht(G: "nx.Graph", r: int, exact: bool = True) -> dict:
    """
    Check whether the Holroyd–Talbot conjecture holds for (G, r).

    Returns a dict:
        {
            "n": int, "mu": int, "r": int,
            "num_indep_sets": int,
            "max_star": int, "max_star_vertex": ...,
            "max_intersecting_family": int,
            "ht_holds": bool,
        }

    If exact=False, uses the star size as an upper-bound proxy (always says True).
    """
    indep = independent_sets_of_size(G, r)
    m = mu(G)
    max_s, max_v = max_star_size(G, indep)
    if exact and indep:
        max_fam = max_intersecting_family_size(indep)
    else:
        max_fam = max_s  # conservative
    return {
        "n": G.number_of_nodes(),
        "mu": m,
        "r": r,
        "num_indep_sets": len(indep),
        "max_star": max_s,
        "max_star_vertex": max_v,
        "max_intersecting_family": max_fam,
        "ht_holds": max_fam <= max_s,
    }


def verify_ht_all_r(G: "nx.Graph", exact: bool = True) -> List[dict]:
    """
    Run verify_ht(G, r) for all valid r (1 ≤ r ≤ μ(G)//2).
    Returns list of result dicts (empty if μ(G) < 2).
    """
    m = mu(G)
    return [verify_ht(G, r, exact=exact) for r in range(1, m // 2 + 1)]
