"""S044 independent Burnside orbit counts and Lean table cross-check."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from s044_burnside import (  # noqa: E402
    burnside_rows, cycle_multiplicity, edge_orbits,
    partitions, type_representative,
)


class S044BurnsideTests(unittest.TestCase):
    def test_small_graph_sequences(self):
        # All unlabeled graphs and connected unlabeled graphs on n vertices.
        expected_all = (1, 2, 4, 11, 34, 156)
        expected_conn = (1, 1, 2, 6, 21, 112)
        for n in range(1, 7):
            with self.subTest(n=n):
                _, result = burnside_rows(n)
                self.assertEqual(result, (expected_all[n-1], expected_conn[n-1]))

    def test_six_vertex_cycle_type_rows(self):
        # Independent finite table copied to the S044 Lean arithmetic checker.
        expected = [
            ((1, 1, 1, 1, 1, 1), 1, 15, 32768, 26704),
            ((1, 1, 1, 1, 2), 15, 11, 2048, 1456),
            ((1, 1, 1, 3), 40, 7, 128, 76),
            ((1, 1, 2, 2), 45, 9, 512, 344),
            ((1, 1, 4), 90, 5, 32, 16),
            ((1, 2, 3), 120, 5, 32, 16),
            ((1, 5), 144, 3, 8, 4),
            ((2, 2, 2), 15, 9, 512, 416),
            ((2, 4), 90, 5, 32, 20),
            ((3, 3), 40, 5, 32, 25),
            ((6,), 120, 3, 8, 5),
        ]
        rows, result = burnside_rows(6)
        self.assertEqual(rows, expected)
        self.assertEqual(result, (156, 112))
        self.assertEqual(sum(row[1] for row in rows), 720)
        self.assertEqual(sum(row[1] * row[3] for row in rows), 112320)
        self.assertEqual(sum(row[1] * row[4] for row in rows), 80640)

    def test_cycle_orbit_partition(self):
        for n in range(1, 7):
            for parts in partitions(n):
                with self.subTest(n=n, parts=parts):
                    perm = type_representative(parts)
                    self.assertEqual(set(perm), set(range(n)))
                    orbits = edge_orbits(perm)
                    edges = [edge for orbit in orbits for edge in orbit]
                    self.assertEqual(len(edges), n*(n-1)//2)
                    self.assertEqual(len(set(edges)), len(edges))
                    self.assertEqual(cycle_multiplicity(parts) > 0, True)


if __name__ == "__main__":
    unittest.main()
