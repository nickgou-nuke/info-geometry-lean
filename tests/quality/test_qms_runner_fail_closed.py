"""Regression checks for QMS paths that must not synthesize evidence."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path

from tools.qms import gates
from tools.qms.audit_report import build_audit_report, load_audit_report
from tools.qms.gates import run_operator_quick_gate
from tools.qms.qa_record import acceptance_checklist_passed
from tools.qms.roles import Role, RoleContext
from tools.qms.qms_runner import _parse_axiom_spec

ROOT = Path(__file__).resolve().parents[2]


class QMSRunnerFailClosedTests(unittest.TestCase):
    @staticmethod
    def _passing_gate3_checks():
        return gates._Gate3Verification(
            compile_ok=True,
            axiom_audit_ok=True,
            placeholder_scan_ok=True,
            style_ok=True,
            commands_run=["verified test command [exit=0]"],
            command_outputs=["verified test command output"],
        )

    def test_axiom_spec_parser_accepts_documented_five_fields(self) -> None:
        self.assertEqual(
            _parse_axiom_spec("sample:propext:Lean:inherited:true"),
            {
                "theorem_name": "sample",
                "axiom": "propext",
                "origin": "Lean",
                "semantic_role": "inherited",
                "approved": True,
            },
        )

    def test_axiom_spec_parser_uses_safe_default_for_omitted_fields(self) -> None:
        self.assertEqual(
            _parse_axiom_spec("sample:custom:project"),
            {
                "theorem_name": "sample",
                "axiom": "custom",
                "origin": "project",
                "semantic_role": "inherited",
                "approved": False,
            },
        )

    def test_audit_report_loader_returns_validated_report(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "audit.json"
            report = {
                "schema": "info_geometry.qms.audit_report.v1",
                "task_id": "QMS-AUDIT-LOAD-TEST",
                "artifact": "Owner.lean",
                "artifact_sha256": "sha256:test",
                "audit_agent_role": "A-A",
                "verdict": "PASS",
                "files_read": ["Owner.lean"],
                "commands_run": ["lake env lean Owner.lean"],
                "gaps": [],
                "capa": [],
                "scope_label": "finite-stage",
            }
            path.write_text(json.dumps(report), encoding="utf-8")
            self.assertEqual(load_audit_report(path), report)

    def test_audit_report_loader_rejects_missing_fields(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "audit.json"
            path.write_text(
                '{"schema":"info_geometry.qms.audit_report.v1"}',
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "missing required fields"):
                load_audit_report(path)

    def test_quick_gate_is_blocked_without_recorded_evidence(self) -> None:
        result = run_operator_quick_gate(
            RoleContext(role=Role.QA_A, task_id="QMS-FAIL-CLOSED-TEST")
        )
        self.assertFalse(result.passed)
        self.assertEqual(len(result.findings), 12)
        self.assertTrue(all(item.startswith("not evidenced:") for item in result.findings))

    def test_acceptance_checklist_defaults_missing_items_to_false(self) -> None:
        self.assertFalse(acceptance_checklist_passed({}))
        self.assertFalse(acceptance_checklist_passed({"scope_labels_assigned": True}))

    def test_compile_gate_needs_hash_matched_independent_audit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            artifact = Path(tmp) / "src" / "Owner.lean"
            artifact.parent.mkdir()
            artifact.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
            with (
                patch.object(gates, "ROOT", Path(tmp)),
                patch.object(gates, "QMS_ARTIFACT_DIR", Path(tmp) / "qms"),
                patch.object(gates, "_execute_gate3_checks", return_value=self._passing_gate3_checks()),
            ):
                result = gates.gate_3_sterile_compile_and_independent_audit(
                    RoleContext(role=Role.QA_A, task_id="QMS-FAIL-CLOSED-TEST"),
                    task_id="QMS-FAIL-CLOSED-TEST",
                    artifact_path=artifact,
                )
            self.assertFalse(result.passed)
            self.assertIn("independent A-A audit report was not supplied", result.findings)
            report = (Path(tmp) / "qms" / "QMS-FAIL-CLOSED-TEST-gate3_report.json").read_text()
            self.assertIn('"audit_agent_role": "QA-A"', report)
            self.assertIn("verified test command [exit=0]", report)

    def test_compile_gate_rejects_replayed_or_scope_mismatched_audit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            artifact = Path(tmp) / "src" / "Owner.lean"
            artifact.parent.mkdir()
            artifact.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
            base_report = build_audit_report(
                task_id="QMS-OTHER-TASK",
                artifact=str(artifact),
                verdict="PASS",
                files_read=[str(artifact)],
                commands_run=["independent source review"],
                gaps=[],
                capa=[],
                scope_label="finite-stage",
                artifact_sha256=gates._sha256_file(artifact),
            )
            reports = [
                base_report,
                {**base_report, "task_id": "QMS-FAIL-CLOSED-TEST"},
                {**base_report, "task_id": "QMS-FAIL-CLOSED-TEST",
                 "scope_label": "analytic"},
            ]
            with (
                patch.object(gates, "ROOT", Path(tmp)),
                patch.object(gates, "QMS_ARTIFACT_DIR", Path(tmp) / "qms"),
                patch.object(gates, "_execute_gate3_checks", return_value=self._passing_gate3_checks()),
            ):
                for report in reports:
                    result = gates.gate_3_sterile_compile_and_independent_audit(
                        RoleContext(role=Role.QA_A, task_id="QMS-FAIL-CLOSED-TEST"),
                        task_id="QMS-FAIL-CLOSED-TEST",
                        artifact_path=artifact,
                        audit_report=report,
                        scope_label="finite-stage",
                    )
                    self.assertFalse(result.passed)
                    self.assertIn(
                        "A-A report is invalid, stale, cross-task, scope-mismatched, or not passing",
                        result.findings,
                    )

    def test_gate3_repair_split_requirement_blocks_pass(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            artifact = Path(tmp) / "src" / "Owner.lean"
            artifact.parent.mkdir()
            artifact.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
            digest = gates._sha256_file(artifact)
            report = build_audit_report(
                task_id="QMS-REPAIR-SPLIT-TEST",
                artifact=str(artifact),
                verdict="PASS",
                files_read=[str(artifact)],
                commands_run=["independent source review"],
                gaps=[],
                capa=[],
                scope_label="finite-stage",
                artifact_sha256=digest,
            )
            with (
                patch.object(gates, "ROOT", Path(tmp)),
                patch.object(gates, "QMS_ARTIFACT_DIR", Path(tmp) / "qms"),
                patch.object(gates, "_execute_gate3_checks", return_value=self._passing_gate3_checks()),
            ):
                result = gates.gate_3_sterile_compile_and_independent_audit(
                    RoleContext(role=Role.QA_A, task_id="QMS-REPAIR-SPLIT-TEST"),
                    task_id="QMS-REPAIR-SPLIT-TEST",
                    artifact_path=artifact,
                    audit_report=report,
                    scope_label="finite-stage",
                    repair_split_required=True,
                )
            self.assertFalse(result.passed)
            self.assertEqual(result.data["verdict"], "REQUEST_CHANGES")
            self.assertTrue(any("auxiliary lemma split required" in x for x in result.findings))

    def test_gate3_rejects_artifact_changed_during_verification(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            artifact = Path(tmp) / "src" / "Owner.lean"
            artifact.parent.mkdir()
            artifact.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
            def mutate_during_checks(_artifact):
                artifact.write_text("theorem sample : True := by trivial\n", encoding="utf-8")
                return self._passing_gate3_checks()

            with (
                patch.object(gates, "ROOT", Path(tmp)),
                patch.object(gates, "QMS_ARTIFACT_DIR", Path(tmp) / "qms"),
                patch.object(gates, "_execute_gate3_checks", side_effect=mutate_during_checks),
            ):
                result = gates.gate_3_sterile_compile_and_independent_audit(
                    RoleContext(role=Role.QA_A, task_id="QMS-CHANGED-SOURCE-TEST"),
                    task_id="QMS-CHANGED-SOURCE-TEST",
                    artifact_path=artifact,
                )
            self.assertFalse(result.passed)
            self.assertTrue(any("artifact changed during verification" in x for x in result.findings))

    def test_gate3_executor_records_actual_argv_and_working_directory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            artifact = root / "src" / "Owner.lean"
            artifact.parent.mkdir()
            artifact.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
            with (
                patch.object(gates, "ROOT", root),
                patch.object(gates, "_run", return_value=(0, "MODULE_RESULT:PASS", "")) as run,
            ):
                checks = gates._execute_gate3_checks(artifact)

            self.assertTrue(checks.compile_ok)
            self.assertTrue(checks.axiom_audit_ok)
            self.assertTrue(checks.placeholder_scan_ok)
            self.assertTrue(checks.style_ok)
            self.assertEqual(run.call_count, 9)
            first_argv = run.call_args_list[0].args[0]
            self.assertEqual(
                first_argv,
                [
                    "python3",
                    "tools/infra/run_locked_lean.py",
                    "--wait-for-build-lock",
                    "src/Owner.lean",
                ],
            )
            self.assertTrue(all(f"cwd={root}" in item for item in checks.commands_run))
            self.assertTrue(all('argv=["python3"' in item for item in checks.commands_run))

    def test_gate5_python_api_cannot_accept_checklist_assertions(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            artifact = Path(tmp) / "Owner.lean"
            artifact.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
            output = Path(tmp) / "qa.json"
            all_checks = {
                "non_authoring_audit": True,
                "non_authoring_qa_rerun": True,
                "scope_labels_assigned": True,
                "owner_theorem_names_cited": True,
                "dag_hash_fresh": True,
                "external_evidence_scoped": True,
                "no_fake_closure_patterns": True,
                "gaps_recorded_as_bucket3": True,
            }
            result = gates.gate_5_acceptance(
                RoleContext(role=Role.QA_A, task_id="QMS-GATE5-FAIL-CLOSED"),
                task_id="QMS-GATE5-FAIL-CLOSED",
                artifact_path=artifact,
                verdict="ACCEPTED",
                status_tags=["verified_logos"],
                commands_run=["claimed command"],
                command_outputs=["claimed pass"],
                remaining_debt=[],
                axiom_classification=[],
                placeholder_findings=[],
                working_tree_scope="clean",
                compliance_checklist=all_checks,
                out_path=output,
            )
            self.assertFalse(result.passed)
            self.assertTrue(result.data["evidence_packet_required"])
            self.assertFalse(output.exists())

    def test_run_all_does_not_create_acceptance_from_cli_defaults(self) -> None:
        result = subprocess.run(
            [sys.executable, "tools/qms/run_qms.py", "--task-id", "QMS-FAIL-CLOSED-TEST", "run-all"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn("is disabled", result.stderr)
        self.assertIn("no acceptance record was written", result.stderr)

    def test_accept_does_not_treat_check_flags_as_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            artifact = Path(tmp) / "Owner.lean"
            artifact.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
            result = subprocess.run(
                [
                    sys.executable,
                    "tools/qms/run_qms.py",
                    "--task-id",
                    "QMS-FAIL-CLOSED-TEST",
                    "accept",
                    "--artifact",
                    str(artifact),
                    "--verdict",
                    "ACCEPTED",
                    "--check-non-authoring-audit",
                    "true",
                    "--check-non-authoring-qa-rerun",
                    "true",
                    "--check-owner-theorem-names",
                    "true",
                    "--check-dag-hash-fresh",
                    "true",
                    "--check-external-evidence-scoped",
                    "true",
                    "--check-no-fake-closure",
                    "true",
                    "--check-gaps-bucket3",
                    "true",
                    "--status-tag",
                    "kernel_verified",
                ],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
        self.assertEqual(result.returncode, 2)
        self.assertIn("will not treat --check-* declarations as evidence", result.stderr)


if __name__ == "__main__":
    unittest.main()
