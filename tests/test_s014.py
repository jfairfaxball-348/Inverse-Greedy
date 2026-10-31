"""S014: exact projected full-priority-order head recursion.

Tests use the exhaustive permutation oracle; the right-hand side is
computed independently by branching on the first globally drawn vertex.
No floating arithmetic and no input graph assumptions.
"""
import sys
import unittest
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from priority_deletion import complete_order_law


def projected_law(rates, active, retained):
    """Push forward *actual* complete weighted orders under projection."""
    out = {}
    for order, mass in complete_order_law(rates, active).items():
        target = tuple(v for v in order if v in retained)
        out[target] = out.get(target, Fraction(0)) + mass
    return out


def head_projected_law(rates, active, retained):
    """Build the projected law by the first-head equation, not by
    enumerating complete orders of active."""
    total = sum((rates[v] for v in active), Fraction())
    if not active:
        return {(): Fraction(1)}
    result = {}
    for v in active:
        conditional = projected_law(rates, tuple(w for w in active if w != v), retained)
        for tail, weight in conditional.items():
            target = ((v,) + tail) if v in retained else tail
            result[target] = result.get(target, Fraction()) + rates[v] / total * weight
    return result


def first_retained_by_recurrence(rates, active, retained, winner):
    """Recursive first-retained-winner mass (the discarded-first branch
    is not assumed to have the correct law)."""
    active = frozenset(active)
    retained = frozenset(retained)
    if winner not in retained:
        return Fraction()
    @lru_cache(None)
    def rec(remaining):
        total = sum((rates[v] for v in remaining), Fraction())
        if not remaining:
            return Fraction()
        return sum((rates[v] / total *
                    (Fraction(v == winner) if v in retained
                     else rec(remaining - {v}))
                    for v in remaining), Fraction())
    return rec(active)


class WeightedProjectionTests(unittest.TestCase):
    def test_head_recursion_and_complete_projected_distribution(self):
        rates = tuple(Fraction(2*i + 1, i + 2) for i in range(6))
        active = tuple(range(6))
        for k in range(0, 4):
            for kept in combinations(active, k):
                with self.subTest(kept=kept):
                    direct = projected_law(rates, active, frozenset(kept))
                    branched = head_projected_law(rates, active, frozenset(kept))
                    self.assertEqual(direct, branched)
                    self.assertEqual(
                        direct, complete_order_law(rates, kept),
                        "deletion consistency is independently checked, not used"
                    )
                    self.assertEqual(sum(direct.values()), 1)

    def test_first_retained_winner_all_subsets(self):
        rates = tuple(Fraction(i + 1, i + 3) for i in range(6))
        full = complete_order_law(rates)
        for k in range(1, 7):
            for kept in combinations(range(6), k):
                denom = sum((rates[v] for v in kept), Fraction())
                for winner in kept:
                    from_permutations = sum((
                        p for order, p in full.items()
                        if next(v for v in order if v in kept) == winner
                    ), Fraction())
                    from_recursion = first_retained_by_recurrence(
                        rates, range(6), kept, winner
                    )
                    with self.subTest(kept=kept, winner=winner):
                        self.assertEqual(from_permutations, from_recursion)
                        self.assertEqual(from_recursion, rates[winner] / denom)

    def test_empty_retained_and_all_retained(self):
        rates = (Fraction(3, 2), Fraction(2, 7), Fraction(5, 3))
        self.assertEqual(projected_law(rates, (0, 1, 2), set()), {(): 1})
        self.assertEqual(projected_law(rates, (), set()), {(): 1})
        self.assertEqual(
            projected_law(rates, (0, 1, 2), {0, 1, 2}),
            complete_order_law(rates)
        )


if __name__ == "__main__":
    unittest.main()
