"""S043: independent exact permutation partition and atlas crosswalk."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from s043_atlas_crosswalk import (  # noqa: E402
    ALL_PERMS, NUM_CODES, atlas_crosswalk, encode_edges,
    independent_partition_check, relabel_independently,
)
from s042_six_vertex_orbits import enumerate_orbits, is_connected  # noqa: E402


class S043CrosswalkTests(unittest.TestCase):
    def test_all_32768_codes_partition_independently(self):
        representatives, _, _ = enumerate_orbits()
        independent_partition_check(representatives)
        self.assertEqual(len(representatives), 156)
        self.assertEqual(NUM_CODES, 32768)
        self.assertEqual(len(ALL_PERMS), 720)

    def test_every_connected_atlas_graph_has_a_distinct_checked_orbit(self):
        records = atlas_crosswalk()
        self.assertEqual(len(records), 112)
        self.assertEqual([r["atlas_index"] for r in records], list(range(112)))
        self.assertEqual(len({r["representative_code"] for r in records}), 112)
        for row in records:
            self.assertTrue(is_connected(row["atlas_code"]))
            self.assertTrue(is_connected(row["representative_code"]))
            self.assertEqual(relabel_independently(
                row["atlas_code"], row["vertex_to_representative"]),
                row["representative_code"])

    def test_edge_encoding_rejects_invalid_inputs(self):
        self.assertEqual(encode_edges([]), 0)
        self.assertEqual(encode_edges([(0, 1), (2, 4)]), 1 | (1 << 10))
        for edges in ([(0, 0)], [(0, 6)], [(0, 1), (1, 0)]):
            with self.subTest(edges=edges), self.assertRaises(AssertionError):
                encode_edges(edges)
        with self.assertRaises(AssertionError):
            relabel_independently(1, (0, 0, 2, 3, 4, 5))


if __name__ == "__main__":
    unittest.main()
