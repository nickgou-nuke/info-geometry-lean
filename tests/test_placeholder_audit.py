from pathlib import Path

from tools.quality.placeholder_audit import (
    TrustFinding,
    build_json,
    build_signal_payload,
    run_audit,
    scan_lean_file,
)



def test_scan_lean_file_flags_trust_shortcuts(tmp_path: Path) -> None:
    lean_file = tmp_path / "TrustProbe.lean"
    lean_file.write_text(
        """
import Mathlib

axiom ExternalWitness : True

theorem sorry_theorem : True := by
  sorry

theorem trivial_proof : 1 = 1 := by
  trivial
""",
        encoding="utf-8",
    )

    findings = scan_lean_file(lean_file)
    kinds = {item.finding for item in findings}
    severities = {item.severity for item in findings}

    assert "explicit-placeholder-declaration" in kinds
    assert "proof-hole" in kinds
    assert "vacuous-prop-constant" in kinds or "skeletal-proof" in kinds
    assert "hard" in severities
    assert "soft" in severities


def test_run_audit_skips_unstable_when_requested(tmp_path: Path) -> None:
    lean_root = tmp_path / "lean"
    stable = lean_root / "InfoGeometry" / "Core.lean"
    unstable = lean_root / "InfoGeometry" / "Unstable" / "Draft.lean"

    stable.parent.mkdir(parents=True, exist_ok=True)
    unstable.parent.mkdir(parents=True, exist_ok=True)

    stable.write_text(
        """
theorem stable_ok : True := by
  have h : True := by
    exact True.intro
  exact h
""",
        encoding="utf-8",
    )
    unstable.write_text(
        """
axiom unstable_missing : True
""",
        encoding="utf-8",
    )

    modules, _, scanned = run_audit(lean_root, scan_unstable=False)
    assert len(modules) == 0
    assert len(scanned) == 1

    modules_all, _, _ = run_audit(lean_root, scan_unstable=True)
    assert len(modules_all) == 1
    assert modules_all[0].findings[0].finding == "explicit-placeholder-declaration"


def test_build_json_report_shape(tmp_path: Path) -> None:
    lean_root = tmp_path / "lean" / "InfoGeometry"
    file = lean_root / "Core.lean"
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(
        """
import Mathlib

theorem foo : True := by
  trivial
""",
        encoding="utf-8",
    )

    modules, _, scanned = run_audit(lean_root)
    report = build_json(modules, root=lean_root, scanned_count=len(scanned))

    assert report["schema"] == "info_geometry.placeholder_audit.v2"
    assert "summary" in report
    assert report["summary"]["scanned_count"] == 1
    assert report["summary"]["module_count"] == 1


def test_build_signal_payload_maps_hard_and_soft_findings(tmp_path: Path) -> None:
    findings = [
        TrustFinding(
            file="Demo.lean",
            module="Demo",
            line=3,
            declaration_kind="axiom",
            declaration_name="MissingAxiom",
            finding="explicit-placeholder-declaration",
            severity="hard",
            detail="explicit placeholder declaration",
            snippet="axiom MissingAxiom : True",
        ),
        TrustFinding(
            file="Demo.lean",
            module="Demo",
            line=10,
            declaration_kind="theorem",
            declaration_name="soft_theorem",
            finding="skeletal-proof",
            severity="soft",
            detail="skeletal proof",
            snippet="theorem soft_theorem : True := by aesop",
        ),
    ]
    payload = build_signal_payload(findings, root=tmp_path / "lean")

    assert payload["schema"] == "info_geometry.placeholder_audit_signals.v1"
    assert payload["summary"]["finding_count"] == 2
    assert payload["summary"]["autoproof_signal_count"] == 1
    assert payload["summary"]["closure_debt_signal_count"] == 2

    signals = payload["signals"]
    task_kinds = {item["task_hint"] for item in signals}
    signal_kinds = {item["signal"] for item in signals}
    assert "closure.debt.extend" in task_kinds
    assert "leanstral.autoproof" in task_kinds
    assert "closure.debt.extend" in signal_kinds
    assert "leanstral.autoproof.frontier" in signal_kinds


def test_build_json_includes_provenance_and_verdict_fields(tmp_path: Path) -> None:
    findings = [
        TrustFinding(
            file="Demo.lean",
            module="Demo",
            line=3,
            declaration_kind="axiom",
            declaration_name="MissingAxiom",
            finding="explicit-placeholder-declaration",
            severity="hard",
            detail="explicit placeholder declaration",
            snippet="axiom MissingAxiom : True",
        ),
        TrustFinding(
            file="Demo.lean",
            module="Demo",
            line=10,
            declaration_kind="theorem",
            declaration_name="soft_theorem",
            finding="skeletal-proof",
            severity="soft",
            detail="skeletal proof",
            snippet="theorem soft_theorem : True := by aesop",
        ),
    ]
    from tools.quality.placeholder_audit import ModuleAudit

    module = ModuleAudit(
        path="Demo.lean",
        module="Demo",
        finding_count=2,
        hard_count=1,
        soft_count=1,
        advisory_count=0,
        findings=findings,
    )
    payload = build_json([module], root=tmp_path / "lean", scanned_count=1)

    assert payload["schema"] == "info_geometry.placeholder_audit.v2"
    assert payload["authority_tier"] == "heuristic-proxy"
    assert payload["summary"]["provenance"]["hard_failures"] == 1
    assert payload["summary"]["provenance"]["soft_findings"] == 1

    first = payload["modules"][0]["findings"][0]
    assert "graph_grounded_signal" in first
    assert "heuristic_signal" in first
    assert "hard_verdict_allowed" in first
