"""S045 regression tests for the local Palomar structural preflight."""
import tempfile
import unittest
from pathlib import Path

from experiments.palomar_preflight import inspect_repository, _has_module_header


def make_fixture(root: Path) -> None:
    (root / "LICENSE").write_text("fixture licence only\n")
    (root / "lakefile.toml").write_text('name = "Fixture"\n')
    (root / "lake-manifest.json").write_text("{}\n")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0-rc3\n")
    (root / "Challenge.lean").write_text("module\npublic import Mathlib\ntheorem Fixture.t : True := by sorry\n")
    (root / "Solution.lean").write_text("module\npublic import Mathlib\ntheorem Fixture.t : True := by trivial\n")
    (root / "comparator.json").write_text(
        '{"challenge_module":"Challenge","solution_module":"Solution",'
        '"theorem_names":["Fixture.t"],"definition_names":[],'
        '"permitted_axioms":["propext","Classical.choice","Quot.sound"]}'
    )
    (root / "formalization.yaml").write_text('version: "v0.4"\n')


class S045Preflight(unittest.TestCase):
    def test_module_header_recognition(self):
        self.assertTrue(_has_module_header("-- comment\nmodule\npublic import Mathlib"))
        self.assertTrue(_has_module_header("/- comment -/\nmodule\nimport Mathlib"))
        self.assertFalse(_has_module_header("import Mathlib\nmodule"))
        self.assertFalse(_has_module_header("namespace X\nmodule"))

    def test_good_synthetic_structure_does_not_claim_comparator(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            make_fixture(root)
            result = inspect_repository(root)
            self.assertEqual(result["status"], "STATIC_PREFLIGHT_PASSED")
            self.assertTrue(result["not_verified"])

    def test_root_licence_is_required_even_with_nested_project(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            make_fixture(root)
            (root / "LICENSE").unlink()
            result = inspect_repository(root)
            self.assertEqual(result["status"], "BLOCKED")
            self.assertTrue(any("licence" in f for f in result["failures"]))

    def test_all_lean_files_are_scanned_including_unused(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            make_fixture(root)
            deep = root / "Unused"
            deep.mkdir()
            (deep / "Old.lean").write_text("import Mathlib\n")
            result = inspect_repository(root)
            self.assertEqual(result["status"], "BLOCKED")
            self.assertTrue(any("Unused/Old.lean" in f for f in result["failures"]))

    def test_challenge_size_limit(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            make_fixture(root)
            (root / "Challenge.lean").write_text("module\n" + "-- x\n" * 1000)
            result = inspect_repository(root)
            self.assertTrue(any("Challenge exceeds" in f for f in result["failures"]))


if __name__ == "__main__":
    unittest.main()
