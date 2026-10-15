"""Regressions for source-level proof-debt scan coverage."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "axiom_audit_under_test", ROOT / "tools/infra/axiom_audit.py"
)
assert SPEC is not None and SPEC.loader is not None
audit = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = audit
SPEC.loader.exec_module(audit)


class AxiomAuditScannerTests(unittest.TestCase):
    def test_line_comment_does_not_hide_later_axiom_or_hole(self) -> None:
        source = "-- prose sorry\nprivate axiom hidden : False\ntheorem gap : True := by sorry\n"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Owner.lean"
            path.write_text(source, encoding="utf-8")
            result = audit.scan_file(path)
        self.assertEqual(result["axiom_lines"], [2])
        self.assertEqual(result["sorry_lines"], [3])
        self.assertFalse(result["clean"])

    def test_qualified_tokens_and_quoted_names_are_not_proof_holes(self) -> None:
        source = """def qualifiedA := DAG.Morphism.sorry
def qualifiedB := DAG.Morphism.admit
def reverseQualifiedA := sorry.foo
def reverseQualifiedB := admit.bar
def quoted := ``Lean.Parser.Term.«sorry»
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Names.lean"
            path.write_text(source, encoding="utf-8")
            result = audit.scan_file(path)
        self.assertEqual(result["sorry_lines"], [])
        self.assertEqual(result["admit_lines"], [])

    def test_missing_or_undecodable_files_are_reported_as_coverage_failures(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            missing = Path(directory) / "Missing.lean"
            invalid = Path(directory) / "Invalid.lean"
            invalid.write_bytes(b"\xff")
            results, failures = audit.scan_files([missing, invalid])
        self.assertEqual(results, [])
        self.assertEqual(len(failures), 2)

    def test_empty_selection_is_a_failed_audit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "audit.json"
            with patch.object(audit, "lean_source_files", return_value=[]), patch.object(
                audit, "OUTPUT_REPORT", report
            ), patch.object(sys, "argv", ["axiom_audit.py"]):
                self.assertEqual(audit.main(), 2)
            self.assertFalse(__import__("json").loads(report.read_text())["coverage_complete"])


if __name__ == "__main__":
    unittest.main()
