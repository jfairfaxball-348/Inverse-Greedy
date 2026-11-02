"""S018: independent exact weighted output-pushforward checks.

Two algorithms are compared: exhaustive permutations + greedy scan versus
first-arrival dynamic programming. All calculations use Fraction. Tests
are finite regressions, not proof of the Lean all-graph identity.
"""
import unittest
from fractions import Fraction
from itertools import permutations
from functools import lru_cache


def exact_priority_mass(order, rates):
    remaining = sum((rates[i] for i in order), Fraction())
    result = Fraction(1)
    for i in order:
        result *= rates[i] / remaining
        remaining -= rates[i]
    return result


def scan_greedy(order, adjacency):
    result = 0
    for vertex in order:
        if adjacency[vertex] & result == 0:
            result |= 1 << vertex
    return result


def full_output_law(adjacency, rates):
    law = {}
    for order in permutations(range(len(adjacency))):
        output = scan_greedy(order, adjacency)
        law[output] = law.get(output, Fraction()) + exact_priority_mass(order, rates)
    return law


def first_arrival_law(adjacency, rates):
    @lru_cache(None)
    def dp(remaining):
        if remaining == 0:
            return {0: Fraction(1)}
        total = sum((rates[i] for i in range(len(rates))
                     if remaining & (1 << i)), Fraction())
        law = {}
        for v in range(len(rates)):
            if not remaining & (1 << v):
                continue
            kept = remaining & ~(adjacency[v] | (1 << v))
            for suffix, mass in dp(kept).items():
                target = suffix | (1 << v)
                law[target] = law.get(target, Fraction()) + rates[v] / total * mass
        return law
    return dp((1 << len(rates)) - 1)


def undirected_adjacency(n, edges):
    adjacency = [0] * n
    for u, v in edges:
        assert 0 <= u < v < n
        adjacency[u] |= 1 << v
        adjacency[v] |= 1 << u
    return tuple(adjacency)


class GreedyOutputPushforwardTests(unittest.TestCase):
    def test_all_output_targets_including_impossible(self):
        graph_cases = [
            (0, ()),
            (1, ()),
            (5, ()),
            (6, ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5))),
            (6, ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5))),
            (6, tuple((0, i) for i in range(1, 6))),
            (6, tuple((i, j) for i in range(6) for j in range(i+1, 6))),
            (7, ((0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (3, 6), (4, 5))),
            (7, ((0, 1), (0, 2), (1, 3), (2, 4), (4, 5), (5, 6))),
            (7, tuple((i, i+1) for i in range(6))),
        ]
        for n, edges in graph_cases:
            adjacency = undirected_adjacency(n, edges)
            rates = tuple(Fraction((3*i+5)**2, (i+3)*(i+7)) for i in range(n))
            full = full_output_law(adjacency, rates)
            recursion = first_arrival_law(adjacency, rates)
            with self.subTest(n=n, edges=edges):
                self.assertEqual(sum(full.values(), Fraction()), Fraction(1))
                self.assertEqual(sum(recursion.values(), Fraction()), Fraction(1))
                for target in range(1 << n):
                    self.assertEqual(full.get(target, Fraction()),
                                     recursion.get(target, Fraction()))
                for output in full:
                    self.assertEqual(output, scan_greedy(
                        next(order for order in permutations(range(n))
                             if scan_greedy(order, adjacency) == output),
                        adjacency))

    def test_projection_expectation_nonconstant_order_statistic(self):
        rates = tuple(Fraction(i*i+3*i+13, i+5) for i in range(7))
        for kept in [(0, 2, 5), (1, 3, 4, 6), (), (0, 1, 2, 3, 4)]:
            kept_set = frozenset(kept)
            def statistic(order):
                return Fraction(sum((i+1)*(v+2)**2 for i, v in enumerate(order)),
                                7) + Fraction(len(order), 11)
            full = sum((statistic(tuple(v for v in order if v in kept_set)) *
                        exact_priority_mass(order, rates)
                        for order in permutations(range(7))), Fraction())
            retained = sum((statistic(order) * exact_priority_mass(order, rates)
                            for order in permutations(kept)), Fraction())
            with self.subTest(retained=kept):
                self.assertEqual(full, retained)


if __name__ == "__main__":
    unittest.main()
