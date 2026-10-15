"""Regression checks for semantic vacuity scope and anonymous examples."""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from tools.quality import semantic_vacuity_gate as gate


class SemanticVacuityGateTests(unittest.TestCase):
    def test_tracked_scope_accepts_repository_root_and_selects_all_lean_roots(self):
        seen = {}

        def fake_run(command, **kwargs):
            seen["command"] = command
            return type("Result", (), {"stdout": "lean/A.lean\nproofs/B.lean\nlib/C.lean\n"})()

        with patch.object(subprocess, "run", fake_run):
            selected = gate.tracked_lean_files([Path(".")])

        self.assertEqual(selected, [Path("lean/A.lean"), Path("lib/C.lean"), Path("proofs/B.lean")])
        self.assertEqual(seen["command"][-1], ".")

    def test_missing_selected_source_fails_closed(self):
        with (
            patch.object(subprocess, "run", return_value=type("Result", (), {"stdout": "lean/Missing.lean\n"})()),
            patch.object(gate.sys, "argv", ["semantic_vacuity_gate.py", ".", "--tracked", "--fail-on", "none"]),
            contextlib.redirect_stdout(io.StringIO()),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            self.assertEqual(gate.main(), 2)

    def test_error_findings_fail_but_warning_findings_remain_reportable(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            source = Path("lean/Owner.lean")
            report = root / "coverage.json"
            warning = gate.Finding(str(source), 1, "review", "warning", "owner", "review")
            error = gate.Finding(str(source), 1, "blocking", "error", "owner", "must be fixed")

            with (
                patch.object(gate, "tracked_lean_files", return_value=[source]),
                patch.object(gate, "load_patterns", return_value={"version": 1, "categories": {}}),
                patch.object(gate, "audit_file", return_value=[warning]),
                patch.object(gate.sys, "argv", ["semantic_vacuity_gate.py", ".", "--tracked", "--fail-on", "error", "--fail-prefix", "lean/", "--json-out", str(report)]),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(gate.main(), 0)
            report_data = json.loads(report.read_text(encoding="utf-8"))
            self.assertTrue(report_data["coverage_complete"])
            self.assertEqual(report_data["severity_counts"], {"warning": 1})
            self.assertEqual(report_data["blocking_severity_counts"], {"warning": 1})
            self.assertEqual(report_data["findings"][0]["subject"], "owner")

            archive_error = gate.Finding("archive/Fixture.lean", 1, "blocking", "error", "owner", "fixture")
            with (
                patch.object(gate, "tracked_lean_files", return_value=[Path("archive/Fixture.lean")]),
                patch.object(gate, "audit_file", return_value=[archive_error]),
                patch.object(gate.sys, "argv", ["semantic_vacuity_gate.py", ".", "--tracked", "--fail-on", "error", "--fail-prefix", "lean/"]),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(gate.main(), 0)

            with (
                patch.object(gate, "tracked_lean_files", return_value=[Path("lean/Fixture.lean")]),
                patch.object(gate, "audit_file", return_value=[error]),
                patch.object(gate.sys, "argv", ["semantic_vacuity_gate.py", ".", "--tracked", "--fail-on", "error", "--fail-prefix", "lean/"]),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(gate.main(), 1)

from tools.quality.semantic_vacuity_gate import DEFAULT_PATTERNS, audit_text, load_patterns


def trivial_surfaces(source: str):
    categories = load_patterns(DEFAULT_PATTERNS)["categories"]
    return [
        finding
        for finding in audit_text("Fixture.lean", source, categories)
        if finding.category == "trivial_surface"
    ]


class SemanticVacuityExampleTests(unittest.TestCase):
    def test_one_line_and_multiline_trivial_examples_are_review_warnings(self):
        findings = trivial_surfaces(
            "example : True := by trivial\n"
            "example : True := by\n  trivial\n"
        )
        self.assertEqual(
            [(finding.subject, finding.severity) for finding in findings],
            [
                ("<anonymous-example-1>", "warning"),
                ("<anonymous-example-2>", "warning"),
            ],
        )

    def test_example_bodies_do_not_bleed_into_adjacent_theorem_windows(self):
        source = (
            "theorem substantive : 1 = 1 := by\n"
            "  exact Nat.one_eq_one\n"
            "example : True := by trivial\n"
            "theorem later : 2 = 2 := by\n"
            "  exact Nat.two_eq_two\n"
        )
        findings = trivial_surfaces(source)
        self.assertEqual(
            [finding.subject for finding in findings], ["<anonymous-example-1>"]
        )

    def test_meaningful_examples_and_comment_string_mentions_are_not_flagged(self):
        source = '''
-- example : True := by trivial
def sample : String := "example : True := by trivial"
example : 2 + 2 = 4 := by norm_num
 example (n : Nat) : n ≤ n := by omega
'''
        self.assertEqual(trivial_surfaces(source), [])
