"""S011: exact regressions for full-priority order and deletion consistency.

No float tolerances. Both order enumeration methods are independent of
the graph first-choice recursion; positive rates throughout.
"""
import sys
import unittest
from fractions import Fraction
from itertools import combinations, permutations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))

from exact import graph, path, cycle, law_by_recursion, law_by_permutations
from priority_deletion import (
    complete_order_law, projected_order_law, conditional_projected_after_first,
    head_split_orders,
)


class PriorityDeletionTests(unittest.TestCase):
    def test_unique_head_decomposition_and_total_mass(self):
        for n in range(7):
            with self.subTest(n=n):
                orders = head_split_orders(tuple(range(n)))
                self.assertEqual(len(orders), len(set(orders)))
                self.assertEqual(set(orders), set(permutations(range(n))))
                rates = tuple(Fraction(i + 1) for i in range(n))
                law = complete_order_law(rates)
                self.assertEqual(set(law), set(orders))
                self.assertEqual(sum(law.values(), Fraction(0)), 1)

    def test_all_subset_restrictions(self):
        for rates in ((1, 3, 2, 5), (2, 1, 4, 3, 6),
                      (Fraction(1, 2), 3, Fraction(7, 5), 4, 9)):
            n = len(rates)
            for k in range(n+1):
                for keep in combinations(range(n), k):
                    with self.subTest(rates=rates, keep=keep):
                        self.assertEqual(projected_order_law(rates, keep),
                                         complete_order_law(rates, keep))

    def test_conditioned_first_vertex_residual_law(self):
        for rates in ((1, 2, 3, 4), (1, 3, 2, 4, 5)):
            n = len(rates)
            for first in range(n):
                others = tuple(i for i in range(n) if i != first)
                for k in range(len(others)+1):
                    for keep in combinations(others, k):
                        with self.subTest(first=first, keep=keep):
                            self.assertEqual(
                                conditional_projected_after_first(rates, first, keep),
                                complete_order_law(rates, keep),
                            )

    def test_greedy_pushforward_on_diverse_graphs(self):
        graphs = (
            path(5), cycle(5),
            graph(5, ((0, 1), (1, 2), (1, 3), (3, 4))),
            graph(5, ((0, 1), (0, 2), (1, 3), (2, 4), (3, 4))),
            graph(6, ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5))),
        )
        for adj in graphs:
            n = len(adj)
            for rates in ((1,)*n, tuple(range(1, n+1))):
                with self.subTest(n=n, rates=rates, graph=adj):
                    self.assertEqual(law_by_permutations(adj, rates),
                                     law_by_recursion(adj, rates))


if __name__ == "__main__":
    unittest.main()
