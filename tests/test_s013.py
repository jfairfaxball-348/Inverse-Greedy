"""S013 exact regression for weighted first-head conditioning.

Independent exact Fraction arithmetic; no floating optimisation.
The head/tail identity is the next Lean structural step.  The later
projection after deleting blocked vertices is independently checked
against weighted orders of the induced residual set.
"""
import sys
import unittest
from fractions import Fraction
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))

from exact import graph, path, cycle, star
from priority_deletion import complete_order_law, weighted_order_mass


def scan(adj, order):
    accepted = 0
    for v in order:
        if not (adj[v] & accepted):
            accepted |= 1 << v
    return accepted


def keep_after_first(adj, v, order):
    return tuple(w for w in order if w != v and not (adj[v] & (1 << w)))


class WeightedHeadConditioningTests(unittest.TestCase):
    def test_general_weighted_head_sum(self):
        rates = (Fraction(1, 2), 3, Fraction(7, 5), 4, 2, 1)
        for n in range(7):
            for k in range(n + 1):
                if k == 0:
                    continue
                for vertices in combinations(range(n), k):
                    with self.subTest(n=n, vertices=vertices):
                        total = sum((rates[v] for v in vertices), Fraction())
                        # A genuinely head-and-suffix-dependent statistic.
                        def statistic(v, tail):
                            return Fraction(2*v + 1, 3) + sum(
                                (Fraction((i+1)*(w+1), 7) for i, w in enumerate(tail)),
                                Fraction(),
                            )
                        lhs = sum((mass * statistic(order[0], order[1:])
                                   for order, mass in complete_order_law(
                                       rates, vertices).items()), Fraction())
                        rhs = sum((rates[v] / total *
                                   sum((mass * statistic(v, tail)
                                        for tail, mass in complete_order_law(
                                            rates, tuple(w for w in vertices if w != v)
                                        ).items()), Fraction())
                                   for v in vertices), Fraction())
                        self.assertEqual(lhs, rhs)

    def test_conditional_head_is_first_choice_rate(self):
        rates = (1, 2, 5, 3, 7, 11)
        for k in range(1, 7):
            for vertices in combinations(range(6), k):
                law = complete_order_law(rates, vertices)
                denom = sum(rates[v] for v in vertices)
                for v in vertices:
                    with self.subTest(vertices=vertices, first=v):
                        p = sum((w for order, w in law.items()
                                 if order[0] == v), Fraction())
                        self.assertEqual(p, Fraction(rates[v], denom))

    def test_conditional_filtered_tail_is_weighted_residual(self):
        graphs = (graph(5, ()), path(5), cycle(5), star(4),
                  graph(6, ((0,1), (1,2), (2,3), (1,4), (2,5))))
        for adj in graphs:
            n = len(adj)
            rates = tuple(Fraction(i+1, i+2) for i in range(n))
            full = complete_order_law(rates)
            total = sum(rates)
            for v in range(n):
                residual = tuple(w for w in range(n)
                                 if w != v and not (adj[v] & (1 << w)))
                conditional = {}
                for order, p in full.items():
                    if order[0] != v:
                        continue
                    tail = keep_after_first(adj, v, order[1:])
                    self.assertEqual(scan(adj, order),
                                     (1 << v) | scan(adj, tail))
                    conditional[tail] = conditional.get(
                        tail, Fraction()) + p / (rates[v] / total)
                with self.subTest(n=n, first=v):
                    self.assertEqual(
                        conditional, complete_order_law(rates, residual)
                    )


if __name__ == "__main__":
    unittest.main()
