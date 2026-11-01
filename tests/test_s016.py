"""S016: first-retained-winner event, checked by independent exact oracles.

The dynamic programming oracle never uses the expected r_i / R_A law;
it conditions on the actual first draw among all remaining vertices.
The separate complete-order oracle explicitly sums full weighted
permutations. These checks support, but cannot prove, an all-real claim.
"""
import sys
import unittest
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from priority_deletion import complete_order_law


def first_retained_winner_dp(rates, active, retained, winner):
    kept = frozenset(retained)

    @lru_cache(None)
    def rec(remaining):
        if not kept.intersection(remaining):
            return Fraction(0)
        total = sum((rates[v] for v in remaining), Fraction())
        answer = Fraction(0)
        for v in remaining:
            branch = Fraction(v == winner) if v in kept else rec(remaining - {v})
            answer += rates[v] / total * branch
        return answer

    return rec(frozenset(active))


class FirstRetainedWinnerTests(unittest.TestCase):
    def test_arbitrary_retained_sets_nine(self):
        active = tuple(range(9))
        # Strongly unequal positive rates; no floating point operations.
        rates = (Fraction(1, 1000), Fraction(1000), Fraction(7, 13),
                 Fraction(123, 8), Fraction(1, 47), Fraction(23, 5),
                 Fraction(2, 3), Fraction(101, 2), Fraction(11, 17))
        for size in range(10):
            for kept in combinations(active, size):
                mass_total = Fraction(0)
                denom = sum((rates[v] for v in kept), Fraction())
                for winner in active:
                    actual = first_retained_winner_dp(rates, active, kept, winner)
                    expected = rates[winner] / denom if winner in kept else Fraction(0)
                    with self.subTest(kept=kept, winner=winner):
                        self.assertEqual(actual, expected)
                    mass_total += actual
                self.assertEqual(mass_total, int(bool(kept)))

    def test_full_order_independent_oracle(self):
        active = tuple(range(6))
        rates = (Fraction(17, 3), Fraction(1, 101), Fraction(4),
                 Fraction(9, 17), Fraction(5, 2), Fraction(13, 7))
        full = complete_order_law(rates, active)
        self.assertEqual(sum(full.values(), Fraction()), 1)
        for size in range(7):
            for kept in combinations(active, size):
                for winner in active:
                    direct = sum((
                        mass for order, mass in full.items()
                        if next((v for v in order if v in kept), None) == winner
                    ), Fraction())
                    self.assertEqual(direct,
                                     first_retained_winner_dp(
                                         rates, active, kept, winner))

    def test_conditional_discarded_head(self):
        active = tuple(range(7))
        kept = (0, 3, 5)
        rates = tuple(Fraction(2*v + 1, v + 7) for v in active)
        total = sum(rates, Fraction())
        for winner in kept:
            direct = first_retained_winner_dp(rates, active, kept, winner)
            branches = sum((
                rates[v] / total *
                (Fraction(v == winner) if v in kept
                 else first_retained_winner_dp(
                     rates, tuple(x for x in active if x != v),
                     kept, winner))
                for v in active), Fraction())
            self.assertEqual(direct, branches)


if __name__ == "__main__":
    unittest.main()
