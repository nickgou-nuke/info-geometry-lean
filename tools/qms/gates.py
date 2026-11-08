#!/usr/bin/env python3
"""
QMS Gates 0-5 per docs/ALCHEMICAL_QMS_SOP.md sections 6-11 and process map section 5.

Process map:
  Latent bundle / symbolic claim
        |
        v
  [Stage 0] Intake classification and formal intent envelope   (Gate 0)
        |
        v
  [Stage 1] Semantic normalization to Lean objects and owner surfaces   (Gate 1)
        |
        v
  [Stage 2] Theorem contract with honest hypotheses and names   (Gate 2)
        |
        v
  [Stage 3] Sterile compile with narrow imports   (Gate 3)
        |
        v
  [Stage 4] Independent gap audit and countermodel attempt   (Gate 3 continued / A-A)
        |
        v
  [Stage 5] Bounded repair loop with monotonicity controls   (Gate 4 / CAPA)
        |
        v
  [Stage 6] Kernel acceptance, axiom audit, placeholder/style checks   (Gate 5 / QA-A)
        |
        v
  [Stage 7] Release classification and append-only record   (Gate 5)
"""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
    from tools.qms.intent_envelope import (
        build_intent_envelope,
        IntentEnvelopeError,
        write_intent_envelope,
    )
    from tools.qms.roles import (
        Role,
        RoleContext,
        RoleViolationError,
        check_author_not_auditor,
        check_author_not_acceptor,
        forbid_action,
        may_set_status_tag,
        require_role,
    )
    from tools.qms.audit_report import (
        build_audit_report,
        capa_entry,
        gap_entry,
        write_audit_report,
    )
    from tools.qms.qa_record import (
        acceptance_checklist_passed,
        build_qa_record,
        write_qa_record,
    )
    from tools.qms.capa import CAPAStore
else:
    from tools.pathing import repo_root
    from tools.qms.intent_envelope import (
        build_intent_envelope,
        IntentEnvelopeError,
        write_intent_envelope,
    )
    from tools.qms.roles import (
        Role,
        RoleContext,
        RoleViolationError,
        check_author_not_auditor,
        check_author_not_acceptor,
        forbid_action,
        may_set_status_tag,
        require_role,
    )
    from tools.qms.audit_report import (
        build_audit_report,
        capa_entry,
        gap_entry,
        write_audit_report,
    )
    from tools.qms.qa_record import (
        acceptance_checklist_passed,
        build_qa_record,
        write_qa_record,
    )
    from tools.qms.capa import CAPAStore

ROOT = repo_root()
QMS_ARTIFACT_DIR = ROOT / "artifacts" / "qms"

SCOPE_LABELS = {
    "finite-stage",
    "finite-iteration",
    "direct-limit",
    "categorical-colimit",
    "inverse-limit",
    "topological",
    "analytic",
    "external-evidence",
    "open-debt",
}

APPROVED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

PLACEHOLDER_TOKENS = [
    "sorry",
    "admit",
    "Admitted",
    "axiom",
    "Axiom",
    "Parameter",
    "Conjecture",
    "axiomatization",
    "oops",
    "Prop := True",
    ":= True",
    "_True",
    "_holds",
    "_valid",
    "_certificate",
    "_sorryProof",
]


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _sha256_file(path: Path) -> str:
    import hashlib

    h = hashlib.sha256()
    h.update(path.read_bytes())
    return "sha256:" + h.hexdigest()


def _run(cmd: list[str]) -> tuple[int, str, str]:
    result = subprocess.run(cmd, capture_output=True, text=True, check=False, cwd=ROOT)
    return result.returncode, result.stdout.strip(), result.stderr.strip()


@dataclass
class _Gate3Verification:
    compile_ok: bool
    axiom_audit_ok: bool
    placeholder_scan_ok: bool
    style_ok: bool
    commands_run: list[str]
    command_outputs: list[str]


def _execute_gate3_checks(artifact: Path) -> _Gate3Verification:
    """Execute Gate 3 checks locally; callers cannot supply pass booleans."""
    rel = artifact.relative_to(ROOT)
    module = ".".join(Path(*rel.parts[1:]).with_suffix("").parts)
    commands: list[str] = []
    outputs: list[str] = []

    def run(label: str, command: list[str]) -> tuple[int, str, str]:
        rc, out, err = _run(command)
        commands.append(
            f"{label}: argv={json.dumps(command)} cwd={ROOT} [exit={rc}]"
        )
        outputs.append(f"{label}: rc={rc}; stdout={out[:300]}; stderr={err[:300]}")
        return rc, out, err

    lean_rc, _, _ = run("locked Lean file check", [
        "python3", "tools/infra/run_locked_lean.py", "--wait-for-build-lock", str(rel),
    ])
    build_rc, _, _ = run("locked Lake module build", [
        "python3", "tools/infra/run_locked_lake_build.py", "--wait-for-build-lock", module,
    ])

    olean = ROOT / ".lake" / "build" / "lib" / "lean" / Path(*rel.parts[1:]).with_suffix(".olean")
    axiom_rc, axiom_out, _ = run("axiom audit", [
        "python3", "tools/infra/run_locked_lean.py", "--wait-for-build-lock", "--run",
        "tools/infra/axiom_check.lean", str(olean),
    ])
    placeholder_rc, _, _ = run("placeholder audit", [
        "python3", "tools/quality/placeholder_audit.py", "--root", str(artifact),
        "--format", "json", "--strict",
    ])
    vacuity_rc, _, _ = run("semantic vacuity gate", [
        "python3", "tools/quality/semantic_vacuity_gate.py", str(artifact), "--fail-on", "error",
    ])
    no_hypothesis_rc, _, _ = run("no-hypothesis mandate", [
        "python3", "tools/quality/check_no_hypothesis_mandate.py", "--root", str(artifact),
    ])
    hollow_rc, _, _ = run("hollow theorem detector", [
        "python3", "tools/quality/detect_hollow_theorems.py", "--strict", str(artifact),
    ])
    module_doc_rc, _, _ = run("module-doc lint", [
        "python3", "scripts/lint/required/module_doc_lint.py", str(rel),
    ])
    theorem_lint_rc, _, _ = run("theorem lint", [
        "python3", "scripts/lint/required/theorem_lint.py", str(rel),
    ])

    return _Gate3Verification(
        compile_ok=lean_rc == 0 and build_rc == 0,
        axiom_audit_ok=(axiom_rc == 0 and "MODULE_RESULT:" in axiom_out and ":PASS" in axiom_out),
        placeholder_scan_ok=placeholder_rc == 0,
        style_ok=(vacuity_rc == 0 and no_hypothesis_rc == 0 and hollow_rc == 0
                  and module_doc_rc == 0 and theorem_lint_rc == 0),
        commands_run=commands,
        command_outputs=outputs,
    )


def _lean_files_under(path: Path) -> list[Path]:
    if path.is_file() and path.suffix == ".lean":
        return [path]
    if path.is_dir():
        return sorted(p for p in path.rglob("*.lean") if p.is_file())
    return []


@dataclass
class GateResult:
    gate: int
    name: str
    passed: bool
    task_id: str
    evidence: list[str] = field(default_factory=list)
    findings: list[str] = field(default_factory=list)
    next_gate: int | None = None
    status_tag: str | None = None
    data: dict[str, Any] = field(default_factory=dict)


class GateError(RuntimeError):
    """Raised when a QMS gate fails and processing must halt."""


def gate_0_intake(
    ctx: RoleContext,
    *,
    task_id: str,
    source_text: str,
    intake_classification: str,
    classification: str,
    mathematical_domain: list[str],
    target_status: str,
    risk_level: str,
    allowed_imports: list[str],
    non_theorem_claims: list[str],
    formal_objects: list[str],
    acceptance_theorems: list[str],
    scope_labels: list[str] | None = None,
    source_paths: list[str] | None = None,
    out_path: Path | None = None,
) -> GateResult:
    """
    Gate 0 — Intake and claim inventory (SOP section 6).

    G-A produces a formal intent envelope. Hard rule: do not write a grand
    theorem surface before extracting the smallest explicit mathematical claim.
    """
    require_role(ctx, Role.G_A)

    if out_path is None:
        out_path = QMS_ARTIFACT_DIR / f"{task_id}-intent_envelope.json"
    QMS_ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)

    try:
        envelope = build_intent_envelope(
            task_id=task_id,
            source_text=source_text,
            intake_classification=intake_classification,
            classification=classification,
            mathematical_domain=mathematical_domain,
            target_status=target_status,
            risk_level=risk_level,
            allowed_imports=allowed_imports,
            non_theorem_claims=non_theorem_claims,
            formal_objects=formal_objects,
            acceptance_theorems=acceptance_theorems,
            scope_labels=scope_labels,
            source_paths=source_paths,
        )
    except IntentEnvelopeError as exc:
        return GateResult(
            gate=0,
            name="intake",
            passed=False,
            task_id=task_id,
            findings=[f"intent envelope validation failed: {exc}"],
            next_gate=None,
        )

    write_intent_envelope(envelope, out_path)
    may_set_status_tag(ctx, "intent_captured")

    return GateResult(
        gate=0,
        name="intake",
        passed=True,
        task_id=task_id,
        evidence=[f"intent envelope written to {out_path}"],
        findings=envelope.get("warnings", []),
        next_gate=1,
        status_tag="intent_captured",
        data={"envelope_path": str(out_path)},
    )


def gate_1_owner_search(
    ctx: RoleContext,
    *,
    task_id: str,
    artifact_path: Path | str,
    search_queries: list[str],
    search_lanes: list[str] | None = None,
    owner_files_read: list[str] | None = None,
    existing_theorem_found: bool = False,
    existing_theorem_name: str | None = None,
    missing_colimit_owner: bool = False,
    bucket_3_obligation: str | None = None,
) -> GateResult:
    """
    Gate 1 — Owner-first search (SOP section 7).

    G-A supplies exact symbols/concepts to search. This gate executes repository
    filename and Lean-source searches, searches available local dependency
    sources, and reads the artifact plus any explicitly named owner files.
    Optional graph/navigation lanes are recorded as requested context, not as
    executed evidence.

    Generation stop conditions:
    - if the owner theorem already exists, stop and report the existing theorem
    - if the claim is false in an existing owner file, stop and emit [rejected_false_surface]
    - if the claim requires a missing colimit/inverse-limit/topology/analytic owner,
      stop and emit [bucket_3_open_debt]
    """
    require_role(ctx, Role.G_A)
    artifact = Path(artifact_path)
    if not artifact.is_absolute():
        artifact = ROOT / artifact
    artifact = artifact.resolve()
    if (
        not artifact.is_file()
        or artifact.suffix != ".lean"
        or not artifact.is_relative_to(ROOT)
        or artifact.relative_to(ROOT).parts[0] not in {"src", "lean"}
    ):
        return GateResult(
            gate=1,
            name="owner_search",
            passed=False,
            task_id=task_id,
            findings=["owner search requires an existing in-repository artifact"],
            next_gate=None,
            status_tag="bucket_3_open_debt",
        )
    queries = [query.strip() for query in search_queries if query.strip()]
    if not queries:
        return GateResult(
            gate=1,
            name="owner_search",
            passed=False,
            task_id=task_id,
            findings=["owner search requires at least one non-empty exact search query"],
            next_gate=None,
            status_tag="bucket_3_open_debt",
        )

    source_roots = [name for name in ("src", "lean", "lib") if (ROOT / name).is_dir()]
    if not source_roots:
        return GateResult(
            gate=1,
            name="owner_search",
            passed=False,
            task_id=task_id,
            findings=["owner search requires an available repository Lean source root"],
            next_gate=None,
            status_tag="bucket_3_open_debt",
        )
    dependency_roots = sorted(
        path for path in (ROOT / ".lake" / "packages").glob("*")
        if path.is_dir()
    ) if (ROOT / ".lake" / "packages").is_dir() else []
    artifact.read_bytes()
    evidence = [f"artifact read: {artifact.relative_to(ROOT)}"]
    findings: list[str] = []

    # Execute and record actual commands. A zero-match ripgrep exit (1) is a
    # successful search; any other nonzero exit indicates a failed search.
    for query in queries:
        file_cmd = ["rg", "--files", *source_roots]
        file_rc, file_out, file_err = _run(file_cmd)
        if file_rc not in (0, 1):
            findings.append(f"repository filename search failed for {query!r}: {file_err}")
        else:
            matches = [line for line in file_out.splitlines() if query in Path(line).name]
            evidence.append(
                f"filename search {query!r}: {len(matches)} path match(es); "
                f"command={json.dumps(file_cmd)}"
            )
            evidence.extend(f"  filename match: {path}" for path in matches[:10])

        if source_roots:
            source_cmd = [
                "rg", "--fixed-strings", "--line-number", "--no-heading",
                "--color", "never", "--max-count", "1", "--glob", "*.lean",
                "--", query, *source_roots,
            ]
            source_rc, source_out, source_err = _run(source_cmd)
            if source_rc not in (0, 1):
                findings.append(f"repository content search failed for {query!r}: {source_err}")
            else:
                lines = source_out.splitlines()
                evidence.append(
                    f"Lean-source search {query!r}: {len(lines)} matching line(s); "
                    f"command={json.dumps(source_cmd)}"
                )
                evidence.extend(f"  source match: {line}" for line in lines[:10])

        if dependency_roots:
            dependency_cmd = [
                "rg", "--fixed-strings", "--line-number", "--no-heading",
                "--color", "never", "--max-count", "1", "--glob", "*.lean",
                "--", query, *(str(path.relative_to(ROOT)) for path in dependency_roots),
            ]
            dep_rc, dep_out, dep_err = _run(dependency_cmd)
            if dep_rc not in (0, 1):
                findings.append(f"local dependency search failed for {query!r}: {dep_err}")
            else:
                lines = dep_out.splitlines()
                evidence.append(
                    f"local dependency search {query!r}: {len(lines)} matching line(s); "
                    f"command={json.dumps(dependency_cmd)}"
                )
                evidence.extend(f"  dependency match: {line}" for line in lines[:10])
        else:
            evidence.append("local dependency search: unavailable (.lake/packages absent)")

    files_to_read = [artifact]
    for path_text in owner_files_read or []:
        path = Path(path_text)
        if not path.is_absolute():
            path = ROOT / path
        path = path.resolve()
        if not path.is_file() or not path.is_relative_to(ROOT):
            findings.append(f"declared owner file is missing or outside repository: {path_text}")
        elif path not in files_to_read:
            # Reading bytes makes this recorded owner-file inspection factual.
            path.read_bytes()
            files_to_read.append(path)
    evidence.extend(
        f"owner file read: {path.relative_to(ROOT)}" for path in files_to_read
    )
    if search_lanes:
        evidence.append(
            "additional navigation lanes requested (not verified by this gate): "
            + ", ".join(search_lanes)
        )

    if findings:
        return GateResult(
            gate=1,
            name="owner_search",
            passed=False,
            task_id=task_id,
            evidence=evidence,
            findings=findings,
            next_gate=None,
            status_tag="bucket_3_open_debt",
        )

    if existing_theorem_found:
        may_set_status_tag(ctx, "payload_ready")
        return GateResult(
            gate=1,
            name="owner_search",
            passed=True,
            task_id=task_id,
            evidence=evidence + ["existing-theorem status supplied by caller; not inferred by search"],
            findings=[
                f"owner theorem already exists: {existing_theorem_name}; stop generation per SOP-001-A"
            ],
            next_gate=None,
            status_tag="payload_ready",
        )

    if missing_colimit_owner:
        may_set_status_tag(ctx, "bucket_3_open_debt")
        return GateResult(
            gate=1,
            name="owner_search",
            passed=True,
            task_id=task_id,
            evidence=evidence + ["missing-owner status supplied by caller; not inferred by search"],
            findings=[
                f"missing colimit/inverse-limit/topology/analytic owner: {bucket_3_obligation or 'unspecified'}"
            ],
            next_gate=None,
            status_tag="bucket_3_open_debt",
        )

    may_set_status_tag(ctx, "payload_ready")
    return GateResult(
        gate=1,
        name="owner_search",
        passed=True,
        task_id=task_id,
        evidence=evidence,
        findings=[],
        next_gate=2,
        status_tag="payload_ready",
    )


def gate_2_generation_controls(
    ctx: RoleContext,
    *,
    task_id: str,
    artifact_path: Path | str,
) -> GateResult:
    """
    Gate 2 — Generation controls (SOP section 8).

    This gate executes artifact-scoped static checks. Deeper semantic controls
    are explicitly deferred to the independent Gate 3 audit; they are never
    reported as passed merely because the caller supplied default booleans.
    """
    require_role(ctx, Role.G_A)
    artifact = Path(artifact_path)
    if not artifact.is_absolute():
        artifact = ROOT / artifact
    artifact = artifact.resolve()
    if (
        not artifact.is_file()
        or artifact.suffix != ".lean"
        or not artifact.is_relative_to(ROOT)
        or artifact.relative_to(ROOT).parts[0] not in {"src", "lean"}
    ):
        return GateResult(
            gate=2,
            name="generation_static_scan",
            passed=False,
            task_id=task_id,
            findings=["generation controls require an existing in-repository Lean source"],
            next_gate=None,
            status_tag="bucket_3_open_debt",
        )

    source = artifact.read_text(encoding="utf-8")
    from tools.quality.common import strip_lean_comments
    import re

    code = strip_lean_comments(source, preserve_lines=True)
    broad_imports = [
        (line_no, line.strip())
        for line_no, line in enumerate(code.splitlines(), start=1)
        if re.match(r"^\s*import\s+(?:Mathlib|InfoGeometry\.All)(?:\s|$)", line)
    ]
    audit_cmd = [
        sys.executable, "tools/quality/placeholder_audit.py", "--root",
        str(artifact), "--format", "json", "--strict",
    ]
    audit_rc, audit_out, audit_err = _run(audit_cmd)
    findings = []
    evidence = [f"artifact read: {artifact.relative_to(ROOT)}"]
    try:
        placeholder_report = json.loads(audit_out)
        summary = placeholder_report["summary"]
        evidence.append(
            "placeholder audit: "
            f"scanned={summary['scanned_count']}, hard={summary['hard_count']}, "
            f"soft={summary['soft_count']}, authority={placeholder_report['authority_tier']}"
        )
    except (json.JSONDecodeError, KeyError, TypeError) as exc:
        placeholder_report = None
        findings.append(f"placeholder audit returned unreadable evidence: {exc}; {audit_err}")
    if audit_rc != 0:
        findings.append("artifact placeholder audit failed")
    if broad_imports:
        findings.extend(
            f"broad import needs explicit contract justification at line {line}: {text}"
            for line, text in broad_imports
        )
    else:
        evidence.append("broad import scan passed (Mathlib and InfoGeometry.All absent)")

    deferred_controls = [
        "hidden theorem debt in structure fields",
        "theorem-name strength versus proposition type",
        "full Zorn/split-octonion LieRing packaging",
        "finite evidence promoted to limit/topological/analytic claims",
        "quotient collapse and preservation of intended distinctions",
        "import justification and namespace leakage beyond broad-import scan",
    ]
    evidence.append(
        "semantic controls deferred to independent A-A Gate 3 audit: "
        + "; ".join(deferred_controls)
    )
    if findings:
        return GateResult(
            gate=2,
            name="generation_controls",
            passed=False,
            task_id=task_id,
            evidence=evidence,
            findings=findings,
            next_gate=None,
            status_tag="bucket_3_open_debt",
            data={"placeholder_report": placeholder_report, "deferred_controls": deferred_controls},
        )

    may_set_status_tag(ctx, "formal_contract_ready")
    return GateResult(
        gate=2,
        name="generation_static_scan",
        passed=True,
        task_id=task_id,
        evidence=evidence,
        findings=["semantic controls remain open for independent A-A review"],
        next_gate=3,
        status_tag="payload_ready",
        data={"placeholder_report": placeholder_report, "deferred_controls": deferred_controls},
    )


def gate_3_sterile_compile_and_independent_audit(
    ctx: RoleContext,
    *,
    task_id: str,
    artifact_path: Path | str,
    audit_report: dict[str, Any] | None = None,
    capa_records: list[dict[str, Any]] | None = None,
    scope_label: str = "open-debt",
    countermodel_found: bool = False,
    repair_split_required: bool = False,
) -> GateResult:
    """
    Gate 3 — Sterile compile + independent gap audit (SOP sections 9, Stages 3-4).

    QA-A / A-A checks:
    - compilation test: clean narrow build of the audited Lean file/module
    - axiom auditing: #print axioms or repo axiom-index tool on final symbols
    - placeholder scan: sorry/admit/axiom/Prop := True/fake certificate fields
    - style conformance: naming, docstrings, namespace conventions
    - AST/AQL/hash/DAG traceability: navigation evidence, not proof

    Audit verdicts: PASS / REQUEST_CHANGES / REJECT
    """
    require_role(ctx, Role.QA_A)
    check_author_not_acceptor(ctx, artifact_path)
    # QA-A must not author theorem content; forbid_action is reserved for
    # when an actual forbidden action is attempted.

    findings: list[str] = []
    evidence: list[str] = [f"artifact: {artifact_path}"]

    artifact_file = Path(artifact_path).resolve()
    valid_artifact = (
        artifact_file.is_file()
        and artifact_file.suffix == ".lean"
        and artifact_file.is_relative_to(ROOT)
        and bool(artifact_file.relative_to(ROOT).parts)
        and artifact_file.relative_to(ROOT).parts[0] in {"lean", "src"}
    )
    if valid_artifact:
        artifact_sha256_before = _sha256_file(artifact_file)
        checks = _execute_gate3_checks(artifact_file)
        artifact_sha256_after = _sha256_file(artifact_file)
        if artifact_sha256_after != artifact_sha256_before:
            findings.append("artifact changed during verification; checked bytes are not stable")
    else:
        artifact_sha256_before = None
        artifact_sha256_after = None
        checks = _Gate3Verification(False, False, False, False, [], [])
        findings.append("Gate 3 requires an existing Lean artifact under lean/ or src/")

    if audit_report is None:
        findings.append("independent A-A audit report was not supplied")
    elif (
        audit_report.get("schema") != "info_geometry.qms.audit_report.v1"
        or audit_report.get("audit_agent_role") != "A-A"
        or audit_report.get("task_id") != task_id
        or audit_report.get("artifact") != str(artifact_path)
        or audit_report.get("artifact_sha256") != artifact_sha256_before
        or audit_report.get("scope_label") != scope_label
        or not isinstance(audit_report.get("files_read"), list)
        or str(artifact_path) not in audit_report.get("files_read", [])
        or not isinstance(audit_report.get("commands_run"), list)
        or not audit_report.get("commands_run")
        or audit_report.get("verdict") != "PASS"
        or audit_report.get("gaps")
    ):
        findings.append(
            "A-A report is invalid, stale, cross-task, scope-mismatched, "
            "or not passing"
        )
    else:
        evidence.append("independent A-A audit report supplied with PASS verdict")

    if not checks.compile_ok:
        findings.append("narrow-import compile failed")
    else:
        evidence.append("kernel build passed in stated module scope")

    if not checks.axiom_audit_ok:
        findings.append("axiom audit found unclassified or unapproved axioms")
    else:
        evidence.append("axiom audit clean or limited to approved/classified foundations")

    if not checks.placeholder_scan_ok:
        findings.append("placeholder scan found unclassified proof-debt markers")
    else:
        evidence.append("placeholder scan clean")

    if not checks.style_ok:
        findings.append("style conformance issues found")
    else:
        evidence.append("style conformance verified")

    if countermodel_found:
        findings.append("bounded countermodel search refuted the target")

    if repair_split_required:
        findings.append("loop monotonicity failed; auxiliary lemma split required")

    # Determine verdict only after all blocking findings have been collected.
    if countermodel_found:
        verdict = "REJECT"
    elif findings:
        verdict = "REQUEST_CHANGES" if checks.compile_ok else "REJECT"
    else:
        verdict = "PASS"

    # Write audit report
    QMS_ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    # This is QA-A's Gate-3 result; preserve the independent A-A report input.
    audit_out = QMS_ARTIFACT_DIR / f"{task_id}-gate3_report.json"

    gaps = []
    capa = list(capa_records or [])

    if audit_report is not None:
        gaps = audit_report.get("gaps", [])
        capa = audit_report.get("capa", capa)
        files_read = list(audit_report.get("files_read", []))
        commands_run = list(audit_report.get("commands_run", []))
    else:
        files_read = [str(artifact_path)]
        commands_run = []

    if str(artifact_path) not in files_read:
        files_read.append(str(artifact_path))
    commands_run.extend(checks.commands_run)

    for f in findings:
        gaps.append(
            gap_entry(
                code="G2" if "compile" in f.lower() else "G4",
                description=f,
                file=str(artifact_path),
                line=0,
                severity="error",
            )
        )

    if verdict == "PASS":
        may_set_status_tag(ctx, "kernel_verified")
        may_set_status_tag(ctx, "axiom_audited")
    elif verdict == "REQUEST_CHANGES":
        # Gate 3 runs as QA-A; only A-A may issue the audit-only gap_report_ready tag.
        may_set_status_tag(ctx, "qa_blocked")
    else:
        may_set_status_tag(ctx, "qa_blocked")

    report = build_audit_report(
        task_id=task_id,
        artifact=str(artifact_path),
        verdict=verdict,
        files_read=files_read,
        commands_run=commands_run,
        gaps=gaps,
        capa=capa,
        scope_label=scope_label,
        artifact_sha256=artifact_sha256_after,
        audit_agent_role="QA-A",
    )
    write_audit_report(report, audit_out)

    # REQUEST_CHANGES is a completed review cycle, not a passing gate.
    passed = verdict == "PASS"
    return GateResult(
        gate=3,
        name="sterile_compile_and_audit",
        passed=passed,
        task_id=task_id,
        evidence=evidence,
        findings=findings,
        next_gate=4 if verdict == "REQUEST_CHANGES" else (None if verdict == "REJECT" else 5),
        status_tag=(
            "qa_blocked" if verdict == "REQUEST_CHANGES" else
            ("kernel_verified" if verdict == "PASS" else "qa_blocked")
        ),
        data={
            "gate3_report_path": str(audit_out),
            "independent_audit_report": audit_report is not None,
            "verdict": verdict,
            "commands_run": checks.commands_run,
            "command_outputs": checks.command_outputs,
        },
    )


def gate_4_capa_loop(
    ctx: RoleContext,
    *,
    task_id: str,
    nonconformance_id: str,
    finding: str,
    root_cause: str,
    corrective_action: str,
    preventive_action: str,
    verification_command: str,
    closure_status: str = "open",
    capa_store: CAPAStore | None = None,
    max_cycles: int = 5,
    current_cycle: int = 1,
) -> GateResult:
    """
    Gate 4 — CAPA loop (SOP section 10).

    For every REQUEST_CHANGES or REJECT finding, record a corrective and
    preventive action. If G-A and A-A alternate on the same gap for more than
    max_cycles cycles without decreasing the unresolved goal count, the
    orchestrator must halt the loop and perform a structural split.
    """
    require_role(ctx, Role.ORCHESTRATOR)

    if capa_store is None:
        capa_store = CAPAStore(ROOT / "artifacts" / "qms" / "capa")

    record = capa_store.create(
        finding=finding,
        root_cause=root_cause,
        corrective_action=corrective_action,
        preventive_action=preventive_action,
        verification_command=verification_command,
        closure_status=closure_status,
        linked_task_id=task_id,
    )

    may_set_status_tag(ctx, "needs_capa")

    loop_halted = current_cycle >= max_cycles
    findings: list[str] = [
        f"CAPA {record.id} created (cycle {current_cycle}/{max_cycles})"
    ]
    evidence: list[str] = [f"CAPA record: {record.id}"]

    if loop_halted:
        findings.append(
            f"loop halted after {max_cycles} cycles — structural split required: "
            "isolate first failing subgoal into auxiliary lemma task; "
            "downgrade parent to [needs_capa] or [bucket_3_open_debt]; "
            "dispatch fresh G-A packet for auxiliary lemma"
        )
        may_set_status_tag(ctx, "repair_split_required")
        return GateResult(
            gate=4,
            name="capa_loop",
            passed=False,
            task_id=task_id,
            evidence=evidence,
            findings=findings,
            next_gate=None,
            status_tag="repair_split_required",
            data={"capa_id": record.id, "loop_halted": True},
        )

    return GateResult(
        gate=4,
        name="capa_loop",
        passed=True,
        task_id=task_id,
        evidence=evidence,
        findings=findings,
        next_gate=5 if closure_status == "verified" else None,
        status_tag="needs_capa",
        data={"capa_id": record.id, "loop_halted": False, "cycle": current_cycle},
    )


def gate_5_acceptance(
    ctx: RoleContext,
    *,
    task_id: str,
    artifact_path: Path | str,
    verdict: str,
    status_tags: list[str],
    commands_run: list[str],
    command_outputs: list[str],
    remaining_debt: list[str],
    axiom_classification: list[dict[str, Any]],
    placeholder_findings: list[dict[str, Any]],
    working_tree_scope: str,
    artifact_sha256: str | None = None,
    requires_capa: bool = False,
    capa_ids: list[str] | None = None,
    compliance_checklist: dict[str, bool] | None = None,
    out_path: Path | None = None,
) -> GateResult:
    """
    Gate 5 — Acceptance testing (SOP section 11).

    QA-A runs the final independent quality gate:
    1. toolchain and environment fingerprint
    2. Lean gates (lake env lean, lake build)
    3. axiom and vacuity gates
    4. placeholder scan
    5. CAS/external lanes labeled as evidence only
    6. AST/AQL/hash/DAG freshness if cited

    Disposition: ACCEPTED / ACCEPTED_WITH_LIMITED_SCOPE / REJECTED
    """
    require_role(ctx, Role.QA_A)
    check_author_not_acceptor(ctx, artifact_path)
    # QA-A must not author content, change scope labels, or accept from summaries;
    # forbid_action is reserved for when an actual forbidden action is attempted.

    # This repository version has no independently validated QA evidence-packet
    # input. The CLI already blocks positive acceptance; keep the Python API from
    # turning caller-supplied checklist booleans into an acceptance certificate.
    if verdict != "REJECTED":
        return GateResult(
            gate=5,
            name="acceptance",
            passed=False,
            task_id=task_id,
            evidence=[],
            findings=[
                "positive acceptance is disabled until a validated QA evidence packet is supplied"
            ],
            next_gate=None,
            status_tag="qa_blocked",
            data={"verdict": "REJECTED", "evidence_packet_required": True},
        )

    if out_path is None:
        out_path = QMS_ARTIFACT_DIR / f"{task_id}-qa.json"
    QMS_ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)

    # Run the minimal compliance checklist (SOP section 17)
    # Missing evidence is a failed check. Never infer that process claims were
    # satisfied merely because a caller omitted the checklist.
    checklist = compliance_checklist or {}
    checklist_passed = acceptance_checklist_passed(checklist)

    if not checklist_passed:
        verdict = "REJECTED"
        may_set_status_tag(ctx, "qa_blocked")
        findings = ["minimal compliance checklist not satisfied"]
    elif verdict == "REJECTED":
        may_set_status_tag(ctx, "rejected_false_surface")
        findings = ["rejected: compile failure, hidden proof debt, or false theorem target"]
    elif "accepted_limited_scope" in status_tags:
        may_set_status_tag(ctx, "accepted_limited_scope")
        findings = ["accepted with limited scope — narrower than initiating claim"]
    else:
        may_set_status_tag(ctx, "verified_logos")
        findings = ["all acceptance criteria met"]

    record = build_qa_record(
        task_id=task_id,
        artifact=str(artifact_path),
        verdict=verdict,
        status_tags=status_tags,
        commands_run=commands_run,
        command_outputs=command_outputs,
        remaining_debt=remaining_debt,
        axiom_classification=axiom_classification,
        placeholder_findings=placeholder_findings,
        working_tree_scope=working_tree_scope,
        artifact_sha256=artifact_sha256 or _sha256_file(Path(artifact_path)) if Path(artifact_path).is_file() else None,
        qa_agent_role="QA-A",
        requires_capa=requires_capa,
        capa_ids=capa_ids,
    )
    write_qa_record(record, out_path)

    passed = verdict in {"ACCEPTED", "ACCEPTED_WITH_LIMITED_SCOPE"} and checklist_passed
    return GateResult(
        gate=5,
        name="acceptance",
        passed=passed,
        task_id=task_id,
        evidence=[f"QA record written to {out_path}"],
        findings=findings,
        next_gate=None,
        status_tag=(
            "verified_logos"
            if verdict == "ACCEPTED"
            else ("accepted_limited_scope" if verdict == "ACCEPTED_WITH_LIMITED_SCOPE" else "rejected_false_surface")
        ),
        data={
            "qa_record_path": str(out_path),
            "verdict": verdict,
            "checklist_passed": checklist_passed,
        },
    )


def run_operator_quick_gate(ctx: RoleContext) -> GateResult:
    """
    Operator checklist reminder (SOP section 18) — 12-point pre-acceptance list.

    This function receives no evidence inputs and therefore cannot validate a
    task. It only reports the checklist items as unevidenced; callers must not
    treat it as a completed gate.
    """
    require_role(ctx, Role.QA_A)

    checks = [
        "git status --short checked",
        "exact owner files read",
        "formal intent envelope captured",
        "scope and risk labels assigned",
        "narrow build or file check run",
        "placeholder scan run",
        "axiom audit run or explicitly not applicable",
        "CAS/external evidence labeled finite/external only",
        "A-A and QA-A are not the authoring context",
        "CAPA closed or BUCKET 3/open debt recorded",
        "theorem names checked for content-descriptive honesty",
        "final checksum and toolchain fingerprint recorded",
    ]

    findings: list[str] = []
    evidence: list[str] = [f"checklist reminder: {len(checks)} points"]

    findings.extend(f"not evidenced: {check}" for check in checks)
    evidence.append("reminder only: no execution evidence was supplied")

    may_set_status_tag(ctx, "qa_blocked")
    return GateResult(
        gate=0,
        name="operator_quick_gate",
        passed=False,
        task_id=ctx.task_id,
        evidence=evidence,
        findings=findings,
        next_gate=5,
        status_tag=None,
        data={"checklist": checks},
    )


__all__ = [
    "GateResult",
    "GateError",
    "gate_0_intake",
    "gate_1_owner_search",
    "gate_2_generation_controls",
    "gate_3_sterile_compile_and_independent_audit",
    "gate_4_capa_loop",
    "gate_5_acceptance",
    "run_operator_quick_gate",
]
