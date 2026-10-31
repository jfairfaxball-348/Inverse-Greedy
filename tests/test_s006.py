"""S006: exact n=6 certificate, independently checked by weighted permutations."""
import sys
import unittest
from fractions import Fraction
from pathlib import Path

import networkx as nx
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import graph, law_by_recursion, law_by_permutations, maximal_independent_sets
from census import enumerate_atlas
from six_vertex_witnesses import SIX_VERTEX_RATIONAL, index_one_closed_form


class S006SixVertexTests(unittest.TestCase):
    def test_index_one_exact_witness(self):
        atlas = [g for g in nx.graph_atlas_g() if len(g) == 6 and nx.is_connected(g)]
        self.assertEqual(len(atlas), 112)
        edges, rates = SIX_VERTEX_RATIONAL[1]
        self.assertEqual({frozenset(e) for e in atlas[1].edges()},
                         {frozenset(e) for e in edges})
        self.assertTrue(all(r > 0 for r in rates))
        adj = graph(6, edges)
        target_masks = (sum(1 << v for v in vertices)
                        for vertices in ((0, 2, 4, 5), (0, 3, 4, 5), (1, 3)))
        self.assertEqual(set(maximal_independent_sets(adj)), set(target_masks))
        recursion = law_by_recursion(adj, rates)
        independent = law_by_permutations(adj, rates)  # all 720 priority orders
        self.assertEqual(recursion, independent)
        self.assertEqual(set(recursion.values()), {Fraction(1, 3)})
        p = index_one_closed_form(3, 6, 4, 5)
        self.assertEqual(p, (Fraction(1, 3),)*3)

    def test_index_one_closed_form_for_other_exact_rates(self):
        edges, _ = SIX_VERTEX_RATIONAL[1]
        adj = graph(6, edges)
        for a,t,u,w in ((1,1,1,1), (2,3,4,6), (3,7,2,5), (3,6,4,5)):
            with self.subTest(a=a,t=t,u=u,w=w):
                ans = law_by_recursion(adj, (a,t,u,w,a,a))
                keys = tuple(sum(1<<v for v in members) for members in
                             ((0,2,4,5), (0,3,4,5), (1,3)))
                self.assertEqual(tuple(ans[k] for k in keys),
                                 index_one_closed_form(a,t,u,w))

    def test_updated_connected_atlas(self):
        rows = list(enumerate_atlas(max_n=6, max_rate=4, include_false_twins=False, include_s008=False, include_s009=False))
        positive = [r for r in rows if r['status'] == 'proved-positive']
        negative = [r for r in rows if r['status'] == 'proved-negative']
        open_rows = [r for r in rows if r['status'] == 'unresolved']
        self.assertEqual((len(positive),len(negative),len(open_rows)), (70,4,69))
        target = next(r for r in rows if (r['n'],r['index']) == (6,1))
        self.assertEqual(target['rates'], [3,6,4,5,3,3])
        self.assertEqual(target['status'], 'proved-positive')


if __name__ == '__main__':
    unittest.main()
