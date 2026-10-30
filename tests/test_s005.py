"""S005: rigorous n=5 atlas completion and independent weighted-order checks."""
import sys
import unittest
from fractions import Fraction
from pathlib import Path

import networkx as nx
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import graph, maximal_independent_sets, law_by_recursion, law_by_permutations
from census import enumerate_atlas
from five_vertex_witnesses import (
    FIVE_VERTEX_RATIONAL, ALGEBRAIC_INDEX, ALGEBRAIC_EDGES,
    ALGEBRAIC_RATES, Q3, quadratic_law_by_recursion, quadratic_law_by_permutations
)


class S005FiveVertexTests(unittest.TestCase):
    def test_six_integer_witnesses_both_exact_oracles(self):
        graphs = [g for g in nx.graph_atlas_g() if len(g)==5 and nx.is_connected(g)]
        self.assertEqual(len(graphs), 21)
        for index, (edges, rates) in FIVE_VERTEX_RATIONAL.items():
            with self.subTest(index=index):
                graph_edges = {frozenset(e) for e in graphs[index].edges()}
                self.assertEqual(graph_edges, {frozenset(e) for e in edges})
                adj = graph(5, edges)
                self.assertTrue(all(r > 0 for r in rates))
                rec = law_by_recursion(adj, rates)
                independent = law_by_permutations(adj, rates)
                expected = set(maximal_independent_sets(adj))
                self.assertEqual(set(rec), expected)
                self.assertEqual(rec, independent)
                self.assertEqual(set(rec.values()), {Fraction(1,len(expected))})

    def test_algebraic_positive_witness_both_exact_oracles(self):
        graphs = [g for g in nx.graph_atlas_g() if len(g)==5 and nx.is_connected(g)]
        self.assertEqual({frozenset(e) for e in graphs[ALGEBRAIC_INDEX].edges()},
                         {frozenset(e) for e in ALGEBRAIC_EDGES})
        # All coefficient pairs are nonnegative and have a positive constant.
        self.assertTrue(all(r.a > 0 and r.b >= 0 for r in ALGEBRAIC_RATES))
        adj = graph(5, ALGEBRAIC_EDGES)
        rec = quadratic_law_by_recursion(adj, ALGEBRAIC_RATES)
        perm = quadratic_law_by_permutations(adj, ALGEBRAIC_RATES)
        self.assertEqual(rec, perm)
        self.assertEqual(set(rec), set(maximal_independent_sets(adj)))
        self.assertEqual(set(rec.values()), {Q3(Fraction(1,4))})

    def test_complete_connected_five_vertex_atlas(self):
        rows = list(enumerate_atlas(max_n=5,max_rate=4))
        five = [r for r in rows if r['n']==5]
        counts = {x: sum(r['status']==x for r in five) for x in
                  ('proved-positive','proved-negative','unresolved')}
        self.assertEqual(counts, {'proved-positive':20,'proved-negative':1,'unresolved':0})
        self.assertEqual([r['index'] for r in five if r['status']=='proved-negative'], [2])


if __name__ == '__main__':
    unittest.main()
