"""Check the exhaustive CLI's actual folder coverage and provenance."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


class AllFoldersInventoryTests(unittest.TestCase):
    def test_exhaustive_cli(self):
        command = Path(__file__).resolve().parents[1] / (
            "tools/quality/counterexample_inventory_all_folders.py")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            names = ["lean/A.lean", ".hidden/A.lean", ".kilo/A.lean",
                     ".lake/packages/demo/A.lean", "external_refs/demo/A.lean",
                     "node_modules/demo/A.lean", "artifacts/A.lean"]
            for name in names + [".git/A.lean"]:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("theorem not_zero : (1 : Nat) ≠ 0 := by decide\n")
            (root / "cycle").symlink_to(root, target_is_directory=True)
            result = subprocess.run(
                [sys.executable, str(command), "--root", str(root), "--json"],
                check=True, capture_output=True, text=True)
            report = json.loads(result.stdout)
        self.assertEqual({row["file"] for row in report["files"]}, set(names))
        self.assertEqual(len(report["candidates"]), len(names))
        self.assertEqual(report["errors"], [])
        self.assertEqual({row["reason"] for row in report["skipped"]},
                         {"git-metadata", "symlink"})
        surfaces = {row["file"]: row["surface"] for row in report["files"]}
        self.assertEqual(surfaces["external_refs/demo/A.lean"], "external-ref")
        self.assertEqual(surfaces[".lake/packages/demo/A.lean"], "dependency-or-build")


if __name__ == "__main__":
    unittest.main()
