"""S038: exact regressions for certified full-order measured-bin reindexing.

These tests use independent rational arithmetic. They validate the
finite combinatorial change of variables and its geometric monomials;
they cannot verify Lean compilation or the continuous-clock limit.
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from math import prod
import unittest


def certify_complete(order, n):
    if len(order) != n or set(order) != set(range(n)):
        raise ValueError("The list must enumerate every coordinate exactly once.")
    return tuple(order)


def gaps_to_bins(gaps):
    running = 0
    result = []
    for position, d in enumerate(gaps):
        running += d
        result.append(position + running)
    return tuple(result)


def assign_bins(order, bins):
    return dict(zip(order, bins))


def monomial(q, assignment):
    return prod((1 - q[i]) * q[i] ** assignment[i] for i in range(len(q)))


def complete_order_direct(q, order, cutoff):
    order = certify_complete(order, len(q))
    return sum(
        (monomial(q, assign_bins(order, bins))
         for bins in combinations(range(cutoff), len(q))),
        Fraction(0),
    )


def complete_order_gap(q, order, cutoff):
    order = certify_complete(order, len(q))
    return sum(
        (monomial(q, assign_bins(order, bins))
         for gaps in product(range(cutoff), repeat=len(q))
         for bins in [gaps_to_bins(gaps)]
         if not bins or bins[-1] < cutoff),
        Fraction(0),
    )


def suffix_factors(q, order):
    order = certify_complete(order, len(q))
    ordered_q = [q[i] for i in order]
    return tuple(prod(ordered_q[a:]) for a in range(len(q)))


def geometric_monomial(q, order, gaps):
    order = certify_complete(order, len(q))
    if len(gaps) != len(q):
        raise ValueError("Wrong gap vector length")
    ordered_q = tuple(q[i] for i in order)
    base = prod((1 - x) * x ** j for j, x in enumerate(ordered_q))
    return base * prod(
        Q ** d for Q, d in zip(suffix_factors(q, order), gaps)
    )


def exact_closed_chamber(q, order):
    ordered_q = tuple(q[i] for i in certify_complete(order, len(q)))
    for x in ordered_q:
        if not (0 < x < 1):
            raise ValueError("All geometric factors must lie in (0,1)")
    base = prod((1 - x) * x ** j for j, x in enumerate(ordered_q))
    den = prod(1 - Q for Q in suffix_factors(q, order))
    return base / den


class S038ExactReindex(unittest.TestCase):
    def test_all_orders_and_boundaries(self):
        samples = tuple(map(Fraction, ("1/2", "2/3", "3/5", "4/7")))
        for n in range(5):
            q = samples[:n]
            for order in permutations(range(n)):
                for cutoff in (0, n + 1, n + 3):
                    self.assertEqual(
                        complete_order_direct(q, order, cutoff),
                        complete_order_gap(q, order, cutoff),
                    )

    def test_independent_monomial_factorisation(self):
        samples = tuple(map(Fraction, ("1/2", "2/5", "3/7", "4/9")))
        for n in range(5):
            q = samples[:n]
            for order in permutations(range(n)):
                for gaps in product(range(3), repeat=n):
                    bins = gaps_to_bins(gaps)
                    direct = monomial(q, assign_bins(order, bins))
                    self.assertEqual(direct, geometric_monomial(q, order, gaps))

    def test_suffix_convergence_factors_and_bounds(self):
        samples = tuple(map(Fraction, ("1/3", "2/5", "3/7", "4/9")))
        for n in range(5):
            q = samples[:n]
            for order in permutations(range(n)):
                for Q in suffix_factors(q, order):
                    self.assertTrue(0 < Q < 1)
                a = complete_order_direct(q, order, n + 1)
                b = complete_order_direct(q, order, n + 4)
                closed = exact_closed_chamber(q, order)
                self.assertLessEqual(a, b)
                self.assertLessEqual(b, closed)
                self.assertTrue(0 < closed <= 1)

    def test_reject_missing_repeated_and_foreign_coordinates(self):
        q = (Fraction(1, 2), Fraction(2, 3), Fraction(3, 5))
        for order in ((0, 1), (0, 0, 2), (0, 1, 3), (), (2, 2, 1)):
            with self.assertRaises(ValueError):
                complete_order_direct(q, order, 5)
            with self.assertRaises(ValueError):
                complete_order_gap(q, order, 5)
            with self.assertRaises(ValueError):
                exact_closed_chamber(q, order)

    def test_empty_and_singleton(self):
        self.assertEqual(complete_order_direct((), (), 0), 1)
        self.assertEqual(complete_order_gap((), (), 0), 1)
        self.assertEqual(exact_closed_chamber((), ()), 1)
        q = (Fraction(2, 3),)
        self.assertEqual(complete_order_direct(q, (0,), 1), Fraction(1, 3))
        self.assertEqual(complete_order_gap(q, (0,), 1), Fraction(1, 3))
        self.assertEqual(exact_closed_chamber(q, (0,)), 1)


if __name__ == "__main__":
    unittest.main()
