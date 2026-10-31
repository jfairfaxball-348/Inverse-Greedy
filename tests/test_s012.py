"""S012 exact state-machine regression for deterministic neighbour erasure.

All graph-neighbour maps used for the main theorem are symmetric.
The tests enumerate ALL suffix priority orders, including unequal rates
in the separate two-oracle law check. Directed counterexample explicitly
shows why symmetry is a necessary hypothesis for this formulation.
"""
import sys
import unittest
from itertools import permutations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import graph, path, cycle, star, law_by_recursion, law_by_permutations


def scan(adj, order, accepted=0):
    """Independent finite-state implementation of sequential acceptance."""
    for v in order:
        if not (adj[v] & accepted):
            accepted |= 1 << v
    return accepted


def without_neighbors(adj, v, order):
    return tuple(w for w in order if not (adj[v] & (1 << w)))


class GreedyBlockedErasureTests(unittest.TestCase):
    def test_empty_graph_and_empty_order(self):
        self.assertEqual(scan((), ()), 0)
        self.assertEqual(law_by_recursion((), ()), {0: 1})
        self.assertEqual(law_by_permutations((), ()), {0: 1})

    def test_first_choice_residual_all_permutations(self):
        graphs = (
            graph(5, ()),
            star(4),
            path(5),
            cycle(5),
            graph(6, ((0, 1), (1, 2), (1, 3), (2, 4), (3, 5))),
        )
        for adj in graphs:
            n = len(adj)
            for v in range(n):
                suffix_vertices = tuple(w for w in range(n) if w != v)
                for tail in permutations(suffix_vertices):
                    kept = without_neighbors(adj, v, tail)
                    with self.subTest(n=n, v=v, tail=tail):
                        self.assertEqual(
                            scan(adj, (v,) + tail),
                            (1 << v) | scan(adj, kept),
                        )

    def test_arbitrary_accepted_seed_and_all_suffix_orders(self):
        adj = cycle(5)
        for v in range(len(adj)):
            tail_vertices = tuple(w for w in range(len(adj)) if w != v)
            for seed in range(1 << len(adj)):
                if not (seed & (1 << v)):
                    continue
                for tail in permutations(tail_vertices):
                    with self.subTest(v=v, seed=seed, tail=tail):
                        self.assertEqual(
                            scan(adj, tail, seed),
                            scan(adj, without_neighbors(adj, v, tail), seed),
                        )
                        self.assertEqual(scan(adj, tail, seed) & seed, seed)

    def test_exact_weighted_output_law_two_oracles(self):
        graphs = (graph(5, ()), star(4), path(5), cycle(5), path(6))
        for adj in graphs:
            n = len(adj)
            for rates in (tuple(range(1, n + 1)),
                          tuple(2*i + 3 for i in range(n))):
                with self.subTest(n=n, rates=rates, adj=adj):
                    self.assertEqual(law_by_permutations(adj, rates),
                                     law_by_recursion(adj, rates))

    def test_asymmetric_neighbour_map_breaks_deletion(self):
        # Vertex 0 says 1 is adjacent, but vertex 1 does not reject 0.
        directed = (0b11, 0b10)
        tail = (1,)
        self.assertNotEqual(scan(directed, (0,) + tail),
                            (1 << 0) | scan(directed,
                                            without_neighbors(directed, 0, tail)))


if __name__ == "__main__":
    unittest.main()
