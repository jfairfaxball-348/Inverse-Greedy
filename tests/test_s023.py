"""S023: exact rational strict-bin chambers for genuine independent Exp clocks.

For positive integer rates a_i and n >= 2 use bins of width
delta = -log(1 - 1/n).  The independent geometric bin indices then
have survival q_i=(1-1/n)**a_i, so their strict sorting chamber has
a closed rational product. Unlike weighted-priority DP this oracle is
built directly from binned continuous exponential survival.
"""
import itertools
import unittest
from fractions import Fraction


def _validate(rates, order, n):
    if type(n) is not int or n < 2:
        raise ValueError("n must be an integer at least two")
    if any(type(r) is not int or r <= 0 for r in rates):
        raise ValueError("all rates must be positive integers")
    if tuple(sorted(order)) != tuple(range(len(rates))):
        raise ValueError("order must be a complete permutation")


def strict_bin_chamber(rates, order, n):
    """Exact geometric-gap sum for k_1>=0 and k_j>=k_(j-1)+1."""
    _validate(rates, order, n)
    q = [Fraction(n - 1, n) ** r for r in rates]
    result = Fraction(1)
    for qi in q:
        result *= 1 - qi
    suffix_product = Fraction(1)
    for index in reversed(order):
        suffix_product *= q[index]
        result /= 1 - suffix_product
        if index != order[0]:
            result *= suffix_product
    return result


def strict_bin_first_step_oracle(rates, order, n):
    """Independent first-bin geometric-memorylessness derivation."""
    _validate(rates, order, n)
    q = [Fraction(n - 1, n) ** r for r in rates]
    result = Fraction(1)
    remaining = tuple(order)
    while len(remaining) > 1:
        head, tail = remaining[0], remaining[1:]
        survivor = Fraction(1)
        for k in tail:
            survivor *= q[k]
        result *= (1 - q[head]) * survivor / (1 - survivor * q[head])
        remaining = tail
    return result


def integer_rate_order_mass(rates, order):
    """Exact theoretical continuous limit (not used by the bin oracle)."""
    _validate(rates, order, 2)
    remaining = sum(rates)
    mass = Fraction(1)
    for k in order:
        mass *= Fraction(rates[k], remaining)
        remaining -= rates[k]
    return mass


def pair_union_collision_bound(rates, n):
    """Universal upper bound on any pair of real arrivals sharing a bin."""
    _validate(rates, tuple(range(len(rates))), n)
    return Fraction(sum(min(a, b) for a, b in itertools.combinations(rates, 2)), n)


class S023ExactChambers(unittest.TestCase):
    def test_recurrence_vs_geometric_gaps(self):
        for rates in ((), (3,), (1, 2), (2, 5, 1), (1, 3, 2, 2),
                      (1, 2, 3, 1, 1)):
            for n in (2, 4, 16):
                for order in itertools.permutations(range(len(rates))):
                    self.assertEqual(strict_bin_chamber(rates, order, n),
                                     strict_bin_first_step_oracle(rates, order, n))

    def test_rigorous_continuous_chamber_enclosures(self):
        # A strict bin chamber is contained in the actual real clock
        # chamber; the difference is at most the pair-collision union.
        for rates in ((), (1,), (1, 7), (1, 2, 3), (2, 3, 1, 4)):
            for n in (2, 4, 16, 64):
                tolerance = pair_union_collision_bound(rates, n)
                all_bin_chambers = Fraction(0)
                for order in itertools.permutations(range(len(rates))):
                    binned = strict_bin_chamber(rates, order, n)
                    continuous = integer_rate_order_mass(rates, order)
                    self.assertLessEqual(binned, continuous)
                    self.assertLessEqual(continuous - binned, tolerance)
                    all_bin_chambers += binned
                self.assertLessEqual(0, 1 - all_bin_chambers)
                self.assertLessEqual(1 - all_bin_chambers, tolerance)

    def test_two_clock_matches_s022_oracle(self):
        from test_s022 import binned_race
        for a, b in ((1, 1), (1, 7), (7, 1), (3, 4)):
            for n in (2, 3, 8, 32):
                x, y, tie = binned_race(a, b, n)
                self.assertEqual(strict_bin_chamber((a, b), (0, 1), n), x)
                self.assertEqual(strict_bin_chamber((a, b), (1, 0), n), y)
                self.assertEqual(1 - x - y, tie)

    def test_validation(self):
        for rates, order, n in (((0, 1), (0, 1), 2),
                                ((2, -1), (0, 1), 2),
                                ((1, 2), (1, 1), 2),
                                ((1, 2), (0, 1), 1),
                                ((1, 2), (0,), 2)):
            with self.assertRaises(ValueError):
                strict_bin_chamber(rates, order, n)


if __name__ == "__main__":
    unittest.main()
