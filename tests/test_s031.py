"""S031 exact independent regressions for pair marginals of full orders.

These Fraction checks are *not* a proof of continuous product-measure
pushforward. FiniteClockPairOrder.lean is the genuine measure theorem;
the full finite exponential sorting-chamber law remains Lean-open.
"""
import itertools
import unittest
from fractions import Fraction


def order_mass(order, rates):
    """Finite exact size-biased order weight, with an empty-order mass 1."""
    remaining = sum((rates[i] for i in order), Fraction(0))
    result = Fraction(1)
    for i in order:
        result *= rates[i] / remaining
        remaining -= rates[i]
    return result


class TestS031FiniteClockPairChecks(unittest.TestCase):
    def test_empty_and_singleton_order(self):
        self.assertEqual(order_mass((), ()), 1)
        for rate in [Fraction(1), Fraction(3, 7), Fraction(101)]:
            self.assertEqual(order_mass((0,), (rate,)), 1)

    def test_all_pair_marginals_from_full_order_distribution(self):
        """Independently sum all discrete order masses for every pair."""
        cases = [
            (Fraction(2), Fraction(7)),
            (Fraction(1), Fraction(5), Fraction(13)),
            (Fraction(3), Fraction(1), Fraction(10), Fraction(7)),
            (Fraction(1), Fraction(2), Fraction(3), Fraction(5), Fraction(8)),
            (Fraction(11), Fraction(1), Fraction(4), Fraction(19),
             Fraction(2), Fraction(7)),
        ]
        for rates in cases:
            n = len(rates)
            orders = list(itertools.permutations(range(n)))
            masses = {p: order_mass(p, rates) for p in orders}
            self.assertEqual(sum(masses.values()), 1)
            for i, j in itertools.permutations(range(n), 2):
                pair_mass = sum(
                    (mass for order, mass in masses.items()
                     if order.index(i) < order.index(j)),
                    Fraction(0),
                )
                self.assertEqual(pair_mass, rates[i] / (rates[i] + rates[j]))
                self.assertEqual(
                    pair_mass + sum(
                        (mass for order, mass in masses.items()
                         if order.index(j) < order.index(i)),
                        Fraction(0),
                    ),
                    1,
                )

    def test_chamber_bound_for_each_required_pair(self):
        rates = tuple(map(Fraction, (1, 3, 9, 2, 15, 4)))
        for order in itertools.permutations(range(len(rates))):
            mass = order_mass(order, rates)
            for a, b in itertools.combinations(order, 2):
                self.assertLessEqual(
                    mass, rates[a] / (rates[a] + rates[b])
                )


if __name__ == "__main__":
    unittest.main()
