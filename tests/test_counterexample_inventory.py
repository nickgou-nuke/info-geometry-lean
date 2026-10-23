"""Regression coverage for recursive navigation, not mathematical validity."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "inventory", Path(__file__).resolve().parents[1] / "tools/quality/counterexample_inventory.py")
inventory = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(inventory)


class InventoryTests(unittest.TestCase):
    def test_comments_strings_unicode_and_anonymous(self):
        source = '''/- theorem not_fake : False := by
          /- lemma not_nested : False := by -/ -/
def message := "theorem not_string : False := by"
-- theorem not_line_comment : False := by
@[simp] private theorem
  not_α : (1 : Nat) ≠ 0 := by decide
theorem «not a valid conjecture» : ¬ False := by simp
example : (1 : Nat) ≠ 0 := by decide
theorem reconstruction : (1 : Nat) = 1 := rfl
'''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Test.lean").write_text(source)
            report = inventory.inventory(root)
        rows = report["candidates"]
        self.assertEqual([r["name"] for r in rows],
                         ["not_α", "«not a valid conjecture»", None])
        self.assertEqual([r["line"] for r in rows], [5, 7, 8])
        self.assertEqual(rows[0]["repair_status"], "requires-owner-and-dependent-review")
        self.assertIn("reconstruction", rows[0]["same_file_positive_name_candidates"])
        self.assertNotIn("positive_companions", rows[0])

    def test_all_folders_provenance_and_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = ["lean/Omega/X.lean", "proofs/X.lean", ".hidden/X.lean",
                     "external_refs/demo/X.lean", ".lake/packages/demo/X.lean",
                     "artifacts/X.lean", ".git/X.lean"]
            for name in paths:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("lemma not_x : ¬ False := by simp\n")
            (root / "loop").symlink_to(root, target_is_directory=True)
            report = inventory.inventory(root)
        self.assertEqual(len(report["files"]), 4)
        self.assertEqual(len(report["candidates"]), 4)
        self.assertEqual(report["errors"], [])
        self.assertEqual({x["reason"] for x in report["skipped"]},
                         {"symlink", "git-metadata", "dependency-or-build", "external-ref"})
        labels = {x["file"]: x["surface"] for x in report["files"]}
        self.assertEqual(labels["lean/Omega/X.lean"], "repo-owned")
        self.assertNotIn("external_refs/demo/X.lean", labels)
        self.assertNotIn(".lake/packages/demo/X.lean", labels)
        self.assertTrue(all(len(x["sha256"]) == 64 for x in report["files"]))

    def test_unreadable_encoding_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Bad.lean").write_bytes(b"\xff")
            report = inventory.inventory(root)
        self.assertEqual(len(report["errors"]), 1)
        self.assertEqual(report["files"], [])


if __name__ == "__main__":
    unittest.main()
