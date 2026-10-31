"""S007: false-twin classification and two independent exact priority oracles."""
import sys
import unittest
from fractions import Fraction
from pathlib import Path

import networkx as nx
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from census import enumerate_atlas
from exact import graph, law_by_recursion, law_by_permutations, maximal_independent_sets
from false_twin import contraction_parent, lift_rates
from five_vertex_witnesses import (
    FIVE_VERTEX_RATIONAL, ALGEBRAIC_INDEX, ALGEBRAIC_RATES, Q3,
    quadratic_law_by_recursion, quadratic_law_by_permutations,
)

NEW_POSITIVE = {
    2: 1, 7: 4, 10: 1, 14: 5, 27: 5, 28: 6, 32: 1,
    33: 5, 43: 9, 45: 4, 48: 5, 54: 11, 59: 6,
    63: 9, 66: 15, 72: 9, 77: 11, 85: 15, 101: 15,
}
NEW_NEGATIVE = {4: 2, 13: 2, 16: 2}


class S007FalseTwinTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        atlas = nx.graph_atlas_g()
        cls.six = [g for g in atlas if len(g) == 6 and nx.is_connected(g)]
        cls.five = [g for g in atlas if len(g) == 5 and nx.is_connected(g)]

    def test_exact_atlas_status(self):
        rows = list(enumerate_atlas(6, 4, include_s008=False))
        counts = {s: sum(row["status"] == s for row in rows)
                  for s in ("proved-positive", "proved-negative", "unresolved")}
        self.assertEqual(counts, {"proved-positive": 89,
                                  "proved-negative": 7, "unresolved": 47})
        six = {row["index"]: row for row in rows if row["n"] == 6}
        for idx, parent in (NEW_POSITIVE | NEW_NEGATIVE).items():
            with self.subTest(index=idx):
                row = six[idx]
                self.assertEqual(row["status"], "proved-negative" if idx in NEW_NEGATIVE
                                 else "proved-positive")
                self.assertEqual(row["contracted_n5_index"], parent)
                pair, p, _ = contraction_parent(self.six[idx], self.five)
                self.assertEqual(row["twin_pair"], list(pair))
                self.assertEqual(p, parent)

    def test_all_19_lifted_certificates_with_two_oracles(self):
        for idx, parent in NEW_POSITIVE.items():
            with self.subTest(index=idx, parent=parent):
                pair, p, reduced = contraction_parent(self.six[idx], self.five)
                self.assertEqual(p, parent)
                parent_rates = (ALGEBRAIC_RATES if parent == ALGEBRAIC_INDEX
                                else FIVE_VERTEX_RATIONAL[parent][1])
                rates = lift_rates(reduced, parent, *pair, self.five, parent_rates)
                adj = graph(6, self.six[idx].edges())
                maximal = maximal_independent_sets(adj)
                if parent == ALGEBRAIC_INDEX:
                    self.assertTrue(all(r.a > 0 and r.b >= 0 for r in rates))
                    a = quadratic_law_by_recursion(adj, rates)
                    b = quadratic_law_by_permutations(adj, rates)
                    expected = Q3(Fraction(1, len(maximal)))
                else:
                    self.assertTrue(all(r > 0 for r in rates))
                    a = law_by_recursion(adj, rates)
                    b = law_by_permutations(adj, rates)
                    expected = Fraction(1, len(maximal))
                self.assertEqual(a, b)
                self.assertEqual(set(a), set(maximal))
                self.assertEqual(set(a.values()), {expected})

    def test_negative_contraction_is_genuine_p5(self):
        for idx in NEW_NEGATIVE:
            with self.subTest(index=idx):
                pair, parent, reduced = contraction_parent(self.six[idx], self.five)
                self.assertEqual(parent, 2)
                self.assertTrue(nx.is_isomorphic(reduced, nx.path_graph(5)))
                self.assertFalse(self.six[idx].has_edge(*pair))


if __name__ == "__main__":
    unittest.main()
