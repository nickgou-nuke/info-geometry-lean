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


def test_scan_lean_file_flags_anonymous_example_proof_hole(tmp_path: Path) -> None:
    lean_file = tmp_path / "AnonymousExample.lean"
    lean_file.write_text(
        """example : True := by
  sorry

theorem named_ok : True := by
  exact True.intro

noncomputable example : True := by
  sorry
""",
        encoding="utf-8",
    )

    findings = scan_lean_file(lean_file)

    holes = [
        item.finding == "proof-hole"
        and item.declaration_kind == "example"
        for item in findings
    ]
    assert sum(holes) == 2, findings
    assert {
        item.declaration_name for item in findings if item.finding == "proof-hole"
    } == {"<anonymous-example-1>", "<anonymous-example-2>"}


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


def test_run_audit_supports_explicit_multi_paths(tmp_path: Path) -> None:
    root = tmp_path / "lean" / "InfoGeometry"
    a_file = root / "A.lean"
    b_file = root / "B.lean"
    ignored = root / "Ignored.lean"
    root.mkdir(parents=True)
    a_file.write_text("axiom extA : True\n", encoding="utf-8")
    b_file.write_text("theorem holeB : True := by sorry\n", encoding="utf-8")
    ignored.write_text("axiom ignoredC : True\n", encoding="utf-8")

    modules, findings, scanned = run_audit(root, paths=[a_file, b_file])

    assert len(scanned) == 2
    assert len(modules) == 2
    assert {Path(p).name for p in scanned} == {"A.lean", "B.lean"}
    decl_names = {item.declaration_name for item in findings}
    assert {"extA", "holeB"}.issubset(decl_names)
    assert "ignoredC" not in decl_names


def test_unified_gate_invokes_placeholder_audit_once(monkeypatch: object, tmp_path: Path) -> None:
    import sys
    from types import SimpleNamespace
    from tools.quality import unified_gate

    recorded: list[list[str]] = []
    monkeypatch.setattr(unified_gate.subprocess, "run", lambda cmd, **kw: recorded.append(list(cmd)) or SimpleNamespace(returncode=0))
    monkeypatch.setattr(unified_gate, "extract_live_decls", lambda paths, out: out.write_text("", encoding="utf-8"))
    monkeypatch.setattr(sys, "argv", ["unified_gate.py", "lean/InfoGeometry/A.lean", "lean/InfoGeometry/B.lean"])

    rc = unified_gate.main()

    assert rc == 0
    placeholder_calls = [cmd for cmd in recorded if "tools/quality/placeholder_audit.py" in cmd]
    assert len(placeholder_calls) == 1
    assert placeholder_calls[0][2:] == ["--strict", "lean/InfoGeometry/A.lean", "lean/InfoGeometry/B.lean"]
