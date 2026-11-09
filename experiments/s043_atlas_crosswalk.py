"""S043: independently validate six-vertex orbit partition and atlas crosswalk.

S042 supplies a permutation to a representative for every 15-bit graph.
This module independently expands all 720 vertex permutations of every
representative, demanding disjoint orbits that cover all 32768 labelled
graphs. NetworkX is an external atlas data source only: no NetworkX
isomorphism checker is trusted. The 112 connected atlas records are
matched to distinct orbits by explicitly checked permutations.

This is exact finite PYTHON evidence, not a Lean proof of exhaustiveness.
Run: python experiments/s043_atlas_crosswalk.py [--emit-json FILE]
"""
import argparse
from functools import lru_cache
from itertools import combinations, permutations
import json

from s042_six_vertex_orbits import enumerate_orbits, is_connected

N = 6
PAIRS = tuple(combinations(range(N), 2))
EDGE_INDEX = {edge: i for i, edge in enumerate(PAIRS)}
ALL_PERMS = tuple(permutations(range(N)))
NUM_CODES = 1 << len(PAIRS)


def relabel_independently(code, sigma):
    """Apply a permutation to edges without S042's swap maps."""
    assert 0 <= code < NUM_CODES and len(sigma) == N
    assert set(sigma) == set(range(N))
    out = 0
    for bit, (u, v) in enumerate(PAIRS):
        if (code >> bit) & 1:
            i, j = sorted((sigma[u], sigma[v]))
            out |= 1 << EDGE_INDEX[i, j]
    return out


def encode_edges(edges):
    code = 0
    for u, v in edges:
        assert 0 <= u < N and 0 <= v < N and u != v
        bit = EDGE_INDEX[tuple(sorted((u, v)))]
        assert not ((code >> bit) & 1), "duplicate edge"
        code |= 1 << bit
    return code


def independent_partition_check(representatives):
    """Check a partition via permutations, independently of S042 BFS."""
    assert len(representatives) == 156
    assert sorted(representatives) == list(representatives)
    visited = bytearray(NUM_CODES)
    for rep in representatives:
        orbit = {relabel_independently(rep, p) for p in ALL_PERMS}
        assert min(orbit) == rep, (rep, min(orbit))
        for code in orbit:
            assert not visited[code], (rep, code, "duplicate orbit")
            visited[code] = 1
    assert all(visited), "uncovered graph code"
    assert sum(is_connected(code) for code in representatives) == 112
    assert len(ALL_PERMS) == 720


@lru_cache(maxsize=1)
def atlas_crosswalk():
    import networkx as nx
    representatives, orbit_ids, witnesses = enumerate_orbits()
    independent_partition_check(representatives)
    six_atlas = [g for g in nx.graph_atlas_g()
                 if g.number_of_nodes() == N and nx.is_connected(g)]
    assert len(six_atlas) == 112
    result = []
    used = set()
    for atlas_index, graph in enumerate(six_atlas):
        assert set(graph.nodes()) == set(range(N))
        code = encode_edges(graph.edges())
        assert is_connected(code)
        orbit_index = orbit_ids[code]
        representative = representatives[orbit_index]
        sigma = witnesses[code]
        assert relabel_independently(code, sigma) == representative
        assert is_connected(representative)
        assert representative not in used, (atlas_index, representative)
        used.add(representative)
        result.append({
            "atlas_index": atlas_index,
            "atlas_code": code,
            "orbit_index": orbit_index,
            "representative_code": representative,
            "vertex_to_representative": list(sigma),
        })
    assert used == {rep for rep in representatives if is_connected(rep)}
    assert len(result) == len(used) == 112
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-json", help="path for verified 112-row bridge")
    args = parser.parse_args()
    records = atlas_crosswalk()
    print("n=6: 32768 covered, 156 canonical orbits, 112 connected atlas bijections")
    if args.emit_json:
        with open(args.emit_json, "w", encoding="utf-8") as file:
            json.dump({"n": N, "pair_order": PAIRS, "atlas_to_orbits": records}, file,
                      indent=2)
        print("wrote", args.emit_json, "(Python exact; not Lean proof)")


if __name__ == "__main__":
    main()
