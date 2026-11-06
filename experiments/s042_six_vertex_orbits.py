"""S042: exact orbit witnesses for all labelled six-vertex simple graphs.

A self-contained pure-Python construction. Every one of the 2^15 labelled
graphs is mapped by an explicit vertex permutation onto its least binary-code
representative, using breadth-first orbit traversal under adjacent swaps.

This verifies a finite computation. It is NOT a Lean kernel certificate and
does NOT determine EGU for any unresolved graph.

Usage:
    python3 experiments/s042_six_vertex_orbits.py
    python3 experiments/s042_six_vertex_orbits.py --emit-json /tmp/n6-orbits.json
"""
from collections import deque
from itertools import combinations
import argparse
import json

N = 6
PAIRS = tuple(combinations(range(N), 2))
EDGE_INDEX = {e: i for i, e in enumerate(PAIRS)}
NUM_GRAPHS = 1 << len(PAIRS)
SWAPS = tuple(
    tuple(i + 1 if j == i else i if j == i + 1 else j for j in range(N))
    for i in range(N - 1)
)
EDGE_SWAPS = tuple(
    tuple(EDGE_INDEX[tuple(sorted((sw[a], sw[b])))] for a, b in PAIRS)
    for sw in SWAPS
)


def swap_graph(code, swap_index):
    """Relabel a 15-bit graph by one adjacent vertex transposition."""
    edge_map = EDGE_SWAPS[swap_index]
    answer = 0
    while code:
        bit = code & -code
        answer |= 1 << edge_map[bit.bit_length() - 1]
        code -= bit
    return answer


def is_connected(code):
    """Six-vertex connectivity by exact bitset flood fill."""
    neighbours = [0] * N
    for j, (a, b) in enumerate(PAIRS):
        if code & (1 << j):
            neighbours[a] |= 1 << b
            neighbours[b] |= 1 << a
    seen = 1
    while True:
        expanded = seen
        for v in range(N):
            if seen & (1 << v):
                expanded |= neighbours[v]
        if expanded == seen:
            return seen == (1 << N) - 1
        seen = expanded


def enumerate_orbits():
    """Return (representative codes, orbit IDs, relabelling witnesses).

    witnesses[code][v] maps vertex v of code to its representative's vertex.
    Every witness is verified against every one of the 15 possible edges.
    """
    representatives = []
    orbit_ids = [None] * NUM_GRAPHS
    witnesses = [None] * NUM_GRAPHS
    for first in range(NUM_GRAPHS):
        if orbit_ids[first] is not None:
            continue
        orbit_id = len(representatives)
        representatives.append(first)
        queue = deque([first])
        orbit_ids[first] = orbit_id
        witnesses[first] = tuple(range(N))
        while queue:
            graph = queue.popleft()
            old_witness = witnesses[graph]
            for j, swap in enumerate(SWAPS):
                nxt = swap_graph(graph, j)
                if orbit_ids[nxt] is None:
                    orbit_ids[nxt] = orbit_id
                    # Since the swap is an involution, compose it with the
                    # existing witness to obtain nxt -> representative.
                    witnesses[nxt] = tuple(old_witness[swap[v]] for v in range(N))
                    queue.append(nxt)
                else:
                    assert orbit_ids[nxt] == orbit_id
    for graph, orbit_id in enumerate(orbit_ids):
        target = representatives[orbit_id]
        permutation = witnesses[graph]
        assert set(permutation) == set(range(N))
        for j, (a, b) in enumerate(PAIRS):
            target_edge = EDGE_INDEX[tuple(sorted((permutation[a], permutation[b])))]
            assert bool(graph & (1 << j)) == bool(target & (1 << target_edge))
    assert len(representatives) == 156
    assert sum(map(is_connected, representatives)) == 112
    assert sum(not is_connected(g) for g in representatives) == 44
    return representatives, orbit_ids, witnesses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-json", help="write exact orbit/witness table for future Lean generation")
    args = parser.parse_args()
    reps, ids, witnesses = enumerate_orbits()
    print("n=6: labelled=32768, unlabeled=156, connected=112, disconnected=44")
    if args.emit_json:
        with open(args.emit_json, "w", encoding="utf-8") as fh:
            json.dump({
                "n": N, "pairs": PAIRS, "representatives": reps,
                "orbit_ids": ids, "vertex_to_representative": witnesses,
            }, fh, separators=(",", ":"))
        print("wrote", args.emit_json, "(ordinary exact computation, not Lean proof)")


if __name__ == "__main__":
    main()
