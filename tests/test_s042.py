"""S042: independent exact Fraction checks of fast-pair star coronas.

These are finite computational regressions, NOT universal Lean proofs.
No NetworkX, SymPy, floating point or production Lean assumptions used.
"""
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from s042_six_vertex_orbits import (  # noqa: E402
    NUM_GRAPHS, enumerate_orbits, is_connected, swap_graph,
)


def finite_greedy_law(n, edges, rates):
    nb = [set() for _ in range(n)]
    for a, b in edges:
        nb[a].add(b)
        nb[b].add(a)

    @lru_cache(None)
    def rec(active):
        if not active:
            return {frozenset(): Fraction(1)}
        total = sum(rates[v] for v in active)
        out = {}
        for v in active:
            for remaining, p in rec(active - {v} - nb[v]).items():
                target = frozenset(remaining | {v})
                out[target] = out.get(target, Fraction(0)) + Fraction(rates[v], total) * p
        return out

    return rec(frozenset(range(n)))


def star(m, t):
    """Hub 0; its leaf 1; spokes 2..m+1; spoke leaves m+2..2m+1."""
    assert m >= 2 and t > 0
    n = 2 * m + 2
    edges = [(0, 1)] + [(0, 2 + i) for i in range(m)]
    edges += [(2 + i, m + 2 + i) for i in range(m)]
    count = 2 ** m + 1
    rates = [t, (count - 1) * t] + [1] * (2 * m)
    return n, edges, rates


def expected_mis(m):
    """One hub option and 2^m subsets of spokes."""
    hub_target = frozenset({0} | {m + 2 + i for i in range(m)})
    targets = {hub_target}
    for subset in range(2 ** m):
        t = {1}
        for i in range(m):
            t.add(2 + i if subset & (1 << i) else m + 2 + i)
        targets.add(frozenset(t))
    return targets


class S042StarCoronaTests(unittest.TestCase):
    def test_exact_uniform_branch_lower_bound(self):
        for m in range(2, 7):
            for t in (Fraction(1), Fraction(3), Fraction(10)):
                with self.subTest(m=m, t=t):
                    n, edges, rates = star(m, t)
                    actual = finite_greedy_law(n, edges, rates)
                    targets = expected_mis(m)
                    N = 2 ** m + 1
                    total = N * t + 2 * m
                    self.assertEqual(set(actual), targets)
                    self.assertEqual(sum(actual.values()), 1)
                    self.assertEqual(len(actual), N)
                    # The hub-first branch contributes t/total to its MIS.
                    # The hub-leaf-first branch contributes
                    # ((N-1)t/total) / (N-1) = t/total to EACH other MIS.
                    for p in actual.values():
                        self.assertGreaterEqual(p, t / total)
                    tv = sum((abs(p - Fraction(1, N)) for p in actual.values()), Fraction()) / 2
                    self.assertLessEqual(tv, Fraction(2 * m, 1) / total)
                    # Strictly positive residual is consistent with IG-N5,
                    # but finite tests do not establish non-EGU in general.
                    self.assertGreater(tv, 0)

    def test_arbitrarily_close_finite_examples(self):
        for m in range(2, 6):
            for epsilon in (Fraction(1, 10), Fraction(1, 100)):
                N = 2 ** m + 1
                t = Fraction(2 * m, N) / epsilon + 1
                n, edges, rates = star(m, t)
                law = finite_greedy_law(n, edges, rates)
                tv = sum((abs(p - Fraction(1, N)) for p in law.values()), Fraction()) / 2
                self.assertLess(tv, epsilon)

    def test_all_32768_edge_sets_have_permutation_witnesses(self):
        reps, orbit_ids, sigmas = enumerate_orbits()
        self.assertEqual(NUM_GRAPHS, 32768)
        self.assertEqual(len(reps), 156)
        self.assertEqual(sum(map(is_connected, reps)), 112)
        self.assertEqual(len(orbit_ids), NUM_GRAPHS)
        self.assertEqual(len(sigmas), NUM_GRAPHS)
        # All 5 generating transpositions preserve orbit membership.
        for graph in range(NUM_GRAPHS):
            for i in range(5):
                self.assertEqual(orbit_ids[graph], orbit_ids[swap_graph(graph, i)])


if __name__ == "__main__":
    unittest.main()
