"""S004 exact certificates: cone over P5 and weighted-order recursion."""
import sys
import unittest
from fractions import Fraction
from itertools import product
from pathlib import Path

import networkx as nx
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from exact import graph, path, law_by_recursion, law_by_permutations
from census import enumerate_atlas


def cone_over_p5():
    return graph(6, list((i, i + 1) for i in range(4)) +
                 list((5, i) for i in range(5)))


class S004Certificates(unittest.TestCase):
    def test_cone_graph_is_connected_atlas_index_68(self):
        cone = nx.path_graph(5)
        cone.add_node(5)
        cone.add_edges_from((5, i) for i in range(5))
        graphs = [g for g in nx.graph_atlas_g()
                  if len(g) == 6 and nx.is_connected(g)]
        self.assertTrue(nx.is_isomorphic(graphs[68], cone))
        rows = [r for r in enumerate_atlas(6, 2)
                if r['n'] == 6 and r['index'] == 68]
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]['status'], 'proved-negative')
        self.assertIn('K1 join P5', rows[0]['certificate'])

    def test_cone_join_factorisation_729_exact_rate_vectors(self):
        p5, cone = path(5), cone_over_p5()
        for r0 in product((1, 2, 3), repeat=6):
            rates = tuple(map(Fraction, r0))
            m = law_by_recursion(p5, rates[:5])
            law = law_by_recursion(cone, rates)
            total_path = sum(rates[:5])
            total = sum(rates)
            self.assertEqual(set(law), set(m) | {1 << 5})
            self.assertEqual(law[1 << 5], rates[5] / total)
            for out, p in m.items():
                self.assertEqual(law[out], total_path * p / total)
            # Strict P5 minor survives the positive common join factor.
            self.assertGreater(law[21] * law[10], law[9] * law[18])
        for r in ((1,) * 6, (2, 3, 5, 7, 11, 13)):
            self.assertEqual(law_by_recursion(cone, r),
                             law_by_permutations(cone, r))


if __name__ == "__main__":
    unittest.main()
