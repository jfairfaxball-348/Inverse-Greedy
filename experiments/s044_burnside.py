"""S044: independent Burnside computation of unlabeled/connected graph counts.

Count invariant graphs for each permutation cycle type, using edge-orbits,
not the S042 canonical-label BFS, S043's all-720 orbit partition, or NetworkX.
Burnside's lemma gives the orbit count. This is exact Python, NOT a Lean
formalisation of Burnside's lemma or the connected graph certificate.
"""
from collections import Counter
from itertools import combinations
from math import factorial


def partitions(n, least=1):
    """Unordered integer partitions, in nondecreasing order."""
    if n == 0:
        yield ()
    for first in range(least, n + 1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def type_representative(parts):
    """One vertex permutation of the requested cycle type."""
    perm = list(range(sum(parts)))
    offset = 0
    for size in parts:
        for i in range(size):
            perm[offset + i] = offset + (i + 1) % size
        offset += size
    return perm


def edge_orbits(perm):
    """Compute the permutation's action on unordered pairs."""
    n = len(perm)
    edges = tuple(combinations(range(n), 2))
    seen = set()
    result = []
    for edge in edges:
        if edge in seen:
            continue
        orbit = []
        current = edge
        while current not in seen:
            seen.add(current)
            orbit.append(current)
            current = tuple(sorted((perm[current[0]], perm[current[1]])))
        assert current == edge, (perm, edge)
        result.append(orbit)
    assert len(seen) == len(edges)
    return result


def is_connected_from_orbits(mask, orbits, n):
    """Connectivity for an invariant graph selected by its edge-orbit bits."""
    assert n >= 1
    neighbours = [0] * n
    for bit, edges in enumerate(orbits):
        if (mask >> bit) & 1:
            for a, b in edges:
                neighbours[a] |= 1 << b
                neighbours[b] |= 1 << a
    seen = 1
    while True:
        new_seen = seen
        for v in range(n):
            if (seen >> v) & 1:
                new_seen |= neighbours[v]
        if new_seen == seen:
            return seen == (1 << n) - 1
        seen = new_seen


def cycle_multiplicity(parts):
    """Conjugacy class size n! / product_i (i^m_i m_i!)."""
    counts = Counter(parts)
    denominator = 1
    for length, number in counts.items():
        denominator *= length ** number * factorial(number)
    n = sum(parts)
    assert factorial(n) % denominator == 0
    return factorial(n) // denominator


def burnside_rows(n):
    """Rows (cycle type, multiplicity, edge orbits, fixed all, fixed connected).

    For a given vertex permutation, each edge orbit may be on or off.
    Enumerating these 2^orbit_count masks gives all invariant graphs.
    The connected part is calculated by independent exact reachability.
    """
    assert 1 <= n <= 6
    result = []
    for parts in partitions(n):
        orbits = edge_orbits(type_representative(parts))
        fixed_all = 2 ** len(orbits)
        fixed_connected = sum(
            is_connected_from_orbits(mask, orbits, n)
            for mask in range(fixed_all)
        )
        result.append(
            (parts, cycle_multiplicity(parts), len(orbits),
             fixed_all, fixed_connected)
        )
    group_order = factorial(n)
    assert sum(row[1] for row in result) == group_order
    all_weight = sum(row[1] * row[3] for row in result)
    connected_weight = sum(row[1] * row[4] for row in result)
    assert all_weight % group_order == 0
    assert connected_weight % group_order == 0
    return result, (all_weight // group_order, connected_weight // group_order)


if __name__ == "__main__":
    for n in range(1, 7):
        rows, counts = burnside_rows(n)
        print(f"n={n}: unlabeled={counts[0]} connected={counts[1]}")
        if n == 6:
            print("type | multiplicity | edge orbits | fixed all | fixed connected")
            for row in rows:
                print(*row, sep=" | ")
