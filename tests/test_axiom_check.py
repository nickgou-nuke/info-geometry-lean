"""Regression tests for the Python-to-Lean axiom checker handoff."""

import subprocess
import unittest
from pathlib import Path
from unittest.mock import patch

from tools.infra import axiom_check


class AxiomCheckerRunnerTests(unittest.TestCase):
    def setUp(self):
        self.olean = axiom_check.OLEAN_DIR / "InfoGeometry" / "Sample.olean"

    @patch("tools.infra.axiom_check.subprocess.run")
    @patch.object(Path, "is_file", return_value=True)
    def test_uses_native_module_reader_under_shared_lock(self, _is_file, run):
        marker = f"MODULE_RESULT:{self.olean.resolve()}:PASS\n"
        run.return_value = subprocess.CompletedProcess([], 0, marker, "✓ all 2 declarations clean")
        result = axiom_check.check_olean_file(self.olean)

        self.assertTrue(result["passed"])
        command = run.call_args.args[0]
        self.assertEqual(command[:3], ["flock", "-x", str(axiom_check.BUILD_LOCK)])
        self.assertEqual(command[3:7], ["lake", "env", "lean", "--run"])
        self.assertEqual(Path(command[7]), axiom_check.LEAN_RUNNER)
        self.assertEqual(Path(command[8]), self.olean.resolve())
        self.assertEqual(run.call_args.kwargs["cwd"], axiom_check.REPO_ROOT)

    @patch("tools.infra.axiom_check.subprocess.run")
    @patch.object(Path, "is_file", return_value=True)
    def test_nonzero_native_runner_is_failure(self, _is_file, run):
        marker = f"MODULE_RESULT:{self.olean.resolve()}:FAIL\n"
        run.return_value = subprocess.CompletedProcess([], 1, marker, "x: disallowed axioms [cheat]")
        result = axiom_check.check_olean_file(self.olean)
        self.assertFalse(result["passed"])
        self.assertEqual(result["returncode"], 1)
        self.assertIn("disallowed axioms", result["stderr"])

    @patch("tools.infra.axiom_check.subprocess.run")
    @patch.object(Path, "is_file", return_value=True)
    def test_batch_preserves_per_module_verdicts(self, _is_file, run):
        second = axiom_check.OLEAN_DIR / "InfoGeometry" / "Other.olean"
        run.return_value = subprocess.CompletedProcess(
            [], 1,
            f"MODULE_RESULT:{self.olean.resolve()}:PASS\nMODULE_RESULT:{second.resolve()}:FAIL\n",
            "Other.decl: disallowed axiom cheat",
        )

        results = axiom_check.check_olean_files([self.olean, second])

        self.assertEqual([item["passed"] for item in results], [True, False])
        self.assertIn(str(second.resolve()), run.call_args.args[0])

    @patch("tools.infra.axiom_check.subprocess.run", side_effect=subprocess.TimeoutExpired("lake", 60))
    @patch.object(Path, "is_file", return_value=True)
    def test_timeout_fails_closed(self, _is_file, _run):
        result = axiom_check.check_olean_file(self.olean, timeout=60)
        self.assertFalse(result["passed"])
        self.assertIn("timeout", result["error"])

    def test_module_name_rejects_traversal(self):
        with self.assertRaises(ValueError):
            axiom_check.module_to_olean("../Outside")

    def test_path_outside_olean_root_is_rejected(self):
        with self.assertRaises(ValueError):
            axiom_check.olean_to_module(Path("/tmp/Evil.olean"))


if __name__ == "__main__":
    unittest.main()
