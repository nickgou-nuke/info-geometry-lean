"""Failure-boundary regressions for the native acceptance runner."""
import builtins
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from tools.infra import check_runtime_acceptance as runner


class AcceptanceEvidenceTests(unittest.TestCase):
    def test_git_inventory_excludes_nested_ignored_content_and_directories(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "lean/.kilo").mkdir(parents=True)
            (root / "lean/Fake.lean").mkdir()
            tracked = root / "lean/Tracked.lean"
            fresh = root / "lean/New.lean"
            tracked.write_text("tracked source")
            fresh.write_text("untracked source")
            (root / "lean/.kilo/Nested.lean").write_text("ignored source")
            (root / ".gitignore").write_text(".kilo/\nlean/Tracked.lean\n")
            subprocess.run(["git", "add", "-f", "lean/Tracked.lean"], cwd=root, check=True)
            self.assertEqual(set(runner.native_lean_sources(root)), {tracked, fresh})
            fresh.unlink()
            self.assertEqual(runner.native_lean_sources(root), [tracked])
            added = root / "lean/Added.lean"
            added.write_text("new source")
            self.assertEqual(set(runner.native_lean_sources(root)), {tracked, added})

    def footprint(self, namespace="Fixture"):
        return "\n".join(
            f"'{namespace}.{head}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for head in runner.HEADS
        )

    def test_exact_quoted_namespace_footprints(self):
        runner.audit(self.footprint("«namespace».«end»"), "namespace.end")

    def test_missing_duplicate_or_forbidden_footprints_fail(self):
        good = self.footprint()
        for text in (good.splitlines()[0], good + "\n" + good.splitlines()[0],
                     good.replace("Quot.sound", "sorryAx")):
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                runner.audit(text, "Fixture")

    def test_diagnostics_fail_even_with_all_footprints(self):
        with self.assertRaises(RuntimeError):
            runner.audit(self.footprint() + "\nwarning: declaration uses sorry", "Fixture")

    def test_suite_output_and_actual_count_are_recorded(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "tests").mkdir()
            out = root / "out"
            out.mkdir()
            (root / "tests/test_acceptance_pass.py").write_text(
                "import unittest\nclass Case(unittest.TestCase):\n"
                " def test_pass(self):\n  print('captured-suite-output')\n  self.assertTrue(True)\n"
            )
            with patch.object(runner, "SUITES", ("acceptance_pass",)):
                rows = runner.runtime_suites(root, out)
            self.assertEqual(rows[0]["collected"], 1)
            self.assertEqual(rows[0]["ran"], 1)
            self.assertEqual(rows[0]["skipped"], 0)
            self.assertIn("captured-suite-output", (out / "test_acceptance_pass.log").read_text())

    def test_skipped_suite_cannot_succeed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "tests").mkdir()
            out = root / "out"
            out.mkdir()
            (root / "tests/test_acceptance_skip.py").write_text(
                "import unittest\nclass Case(unittest.TestCase):\n"
                " @unittest.skip('missing dependency')\n def test_skip(self): pass\n"
            )
            with patch.object(runner, "SUITES", ("acceptance_skip",)):
                with self.assertRaises(RuntimeError):
                    runner.runtime_suites(root, out)
            self.assertEqual(json.loads((out / "runtime-tests.json").read_text())[0]["skipped"], 1)

    def test_helper_import_failure_writes_failed_status(self):
        real_import = builtins.__import__
        def fail_lock(name, *args, **kwargs):
            if name == "tools.build_lock":
                raise ImportError("injected lock helper import failure")
            return real_import(name, *args, **kwargs)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            original_cwd = Path.cwd()
            try:
                with patch.object(sys, "argv", ["checker", "--root", str(root), "--out", "evidence"]), \
                     patch.object(sys, "path", sys.path.copy()), \
                     patch("builtins.__import__", side_effect=fail_lock):
                    with self.assertRaises(ImportError):
                        runner.main()
                status = json.loads((root / "evidence/status.json").read_text())
                self.assertEqual(status["result"], "failed")
                self.assertIn("injected lock helper", status["error"])
            finally:
                runner.os.chdir(original_cwd)


if __name__ == "__main__":
    unittest.main()
