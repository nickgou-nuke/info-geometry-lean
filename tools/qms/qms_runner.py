#!/usr/bin/env python3
"""
QMS runner — CLI orchestrator for the Quality Management System
per docs/ALCHEMICAL_QMS_SOP.md.

Implements the Stage 0-7 process map with role separation (G-A / A-A / QA-A /
Orchestrator) and Gate 0-5. Gate 3 directly invokes these artifact-scoped checks:

  - placeholder_audit.py      (placeholder scan)
  - semantic_vacuity_gate.py  (vacuity scan)
  - axiom_check.lean via the locked Lean wrapper (axiom audit)
  - check_no_hypothesis_mandate.py (artifact-scoped naming/proof-hole scan)
  - detect_hollow_theorems.py (artifact-scoped hollow/trivial theorem scan)
  - semantic_vacuity_gate.py  (artifact-scoped vacuity scan)
  - module_doc_lint.py        (module doc structure)
  - theorem_lint.py           (theorem keyword discipline)
  - placeholder_audit.py      (artifact-scoped placeholder scan)

Repository-wide policy, Pauli, mathfulness, and structural checks remain in
strict-check/lint-all/unified-gate workflows; Gate 3 does not claim their
results. CAPA is a separate Gate 4 command.

Subcommands:
  intent          Build a formal intent envelope (Gate 0, G-A)
  owner-search    Run Gate 1 owner-first search (G-A)
  generation      Run Gate 2 generation controls (G-A)
  compile         Run Gate 3 sterile compile + independent audit (QA-A)
  capa            Create/manage CAPA records (Gate 4, Orchestrator)
  accept          Gate 5; acceptance blocked without a verified QA evidence packet
  quick-gate      Run the operator quick gate (SOP section 18)
  run-all         Disabled: this CLI cannot establish independent gate evidence
  capa-index      Show CAPA index
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
    from tools.qms import (
        intent_envelope as ie,
        roles as r,
        audit_report as ar,
        qa_record as qa,
    )
    from tools.qms.gates import (
        gate_0_intake,
        gate_1_owner_search,
        gate_2_generation_controls,
        gate_3_sterile_compile_and_independent_audit,
        gate_4_capa_loop,
        gate_5_acceptance,
        run_operator_quick_gate,
    )
    from tools.qms.roles import (
        Role,
        RoleContext,
    )
    from tools.qms.capa import CAPAStore
else:
    from tools.pathing import repo_root
    from tools.qms import (
        intent_envelope as ie,
        roles as r,
        audit_report as ar,
        qa_record as qa,
    )
    from tools.qms.gates import (
        gate_0_intake,
        gate_1_owner_search,
        gate_2_generation_controls,
        gate_3_sterile_compile_and_independent_audit,
        gate_4_capa_loop,
        gate_5_acceptance,
        run_operator_quick_gate,
    )
    from tools.qms.roles import (
        Role,
        RoleContext,
    )
    from tools.qms.capa import CAPAStore

ROOT = repo_root()
QMS_ARTIFACT_DIR = ROOT / "artifacts" / "qms"


def _parse_role(value: str) -> Role:
    try:
        return Role(value)
    except ValueError:
        print(f"[qms] invalid role: {value!r}; must be one of {sorted(r.Role.__members__.values(), key=lambda x: x.value)}", file=sys.stderr)
        sys.exit(2)


def _parse_bool(value: str) -> bool:
    return value.lower() in {"true", "1", "yes", "on"}


def _parse_axiom_spec(value: str) -> dict[str, Any]:
    """Parse theorem:axiom:origin[:role[:approved]] without truncating fields."""
    parts = value.split(":", 4)
    if len(parts) < 3:
        raise ValueError(
            f"invalid axiom spec: {value!r} "
            "(expected theorem:axiom:origin[:role[:approved]])"
        )
    theorem_name, axiom, origin = parts[:3]
    semantic_role = parts[3] if len(parts) > 3 and parts[3] else "inherited"
    approved = (
        _parse_bool(parts[4])
        if len(parts) > 4
        else axiom in {"propext", "Classical.choice", "Quot.sound"}
    )
    return {
        "theorem_name": theorem_name,
        "axiom": axiom,
        "origin": origin,
        "semantic_role": semantic_role,
        "approved": approved,
    }


def cmd_intent(args: argparse.Namespace) -> int:
    ctx = RoleContext(role=Role.G_A, task_id=args.task_id)
    source_text = args.source_text
    if args.source_file:
        source_text = Path(args.source_file).read_text(encoding="utf-8")

    result = gate_0_intake(
        ctx,
        task_id=args.task_id,
        source_text=source_text,
        intake_classification=args.intake_classification,
        classification=args.classification,
        mathematical_domain=args.mathematical_domain or [],
        target_status=args.target_status,
        risk_level=args.risk_level,
        allowed_imports=args.allowed_import or [],
        non_theorem_claims=args.non_theorem_claim or [],
        formal_objects=args.formal_object or [],
        acceptance_theorems=args.acceptance_theorem or [],
        scope_labels=args.scope_label or None,
        source_paths=args.source_path or None,
        out_path=args.out,
    )

    for line in result.evidence:
        print(f"  + {line}")
    for f in result.findings:
        print(f"  ! {f}")
    print(f"[qms] gate-0 intent: {'passed' if result.passed else 'failed'} "
          f"(tag={result.status_tag})")
    return 0 if result.passed else 1


def cmd_owner_search(args: argparse.Namespace) -> int:
    ctx = RoleContext(role=Role.G_A, task_id=args.task_id)
    result = gate_1_owner_search(
        ctx,
        task_id=args.task_id,
        artifact_path=args.artifact,
        search_queries=args.query,
        search_lanes=args.search_lane or None,
        owner_files_read=args.owner_file or None,
        existing_theorem_found=_parse_bool(args.existing_theorem_found),
        existing_theorem_name=args.existing_theorem_name,
        missing_colimit_owner=_parse_bool(args.missing_colimit_owner),
        bucket_3_obligation=args.bucket_3_obligation,
    )
    for line in result.evidence:
        print(f"  + {line}")
    for f in result.findings:
        print(f"  ! {f}")
    print(f"[qms] gate-1 owner-search: {'passed' if result.passed else 'failed'} "
          f"(tag={result.status_tag})")
    return 0 if result.passed else 1


def cmd_generation(args: argparse.Namespace) -> int:
    ctx = RoleContext(role=Role.G_A, task_id=args.task_id)
    result = gate_2_generation_controls(
        ctx,
        task_id=args.task_id,
        artifact_path=args.artifact,
    )
    for line in result.evidence:
        print(f"  + {line}")
    for f in result.findings:
        print(f"  ! {f}")
    verdict = "PASS" if result.passed else "FAIL"
    print(f"[qms] gate-2 static-scan: {verdict} "
          f"(semantic review pending; tag={result.status_tag})")
    return 0 if result.passed else 1


def cmd_compile(args: argparse.Namespace) -> int:
    artifact = Path(args.artifact).resolve()
    try:
        rel = artifact.relative_to(ROOT)
    except ValueError:
        print("[qms] artifact must be inside the repository", file=sys.stderr)
        return 2
    if (
        not artifact.is_file()
        or artifact.suffix != ".lean"
        or not rel.parts
        or rel.parts[0] not in {"lean", "src"}
    ):
        print("[qms] compile requires an existing Lean source under lean/ or src/", file=sys.stderr)
        return 2

    independent_audit = None
    if args.audit_report:
        try:
            independent_audit = ar.load_audit_report(Path(args.audit_report))
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            print(f"[qms] invalid A-A audit report: {exc}", file=sys.stderr)
            return 2

    ctx = RoleContext(
        role=Role.QA_A,
        task_id=args.task_id,
        acceptance_targets={artifact},
    )
    result = gate_3_sterile_compile_and_independent_audit(
        ctx,
        task_id=args.task_id,
        artifact_path=artifact,
        audit_report=independent_audit,
        scope_label=args.scope_label or "open-debt",
        countermodel_found=_parse_bool(args.countermodel_found),
        repair_split_required=_parse_bool(args.repair_split_required),
    )

    for line in result.data.get("command_outputs", []):
        print(f"  > {line}")
    for line in result.evidence:
        print(f"  + {line}")
    for finding in result.findings:
        print(f"  ! {finding}")
    print(
        f"[qms] gate-3 compile+audit: {'PASS' if result.passed else 'BLOCKED'} "
        f"(verdict={result.data.get('verdict', 'unknown')})"
    )
    if result.data.get("gate3_report_path"):
        print(f"[qms] QA Gate-3 report: {result.data['gate3_report_path']}")
    return 0 if result.passed else 1

def cmd_capa(args: argparse.Namespace) -> int:
    store = CAPAStore(QMS_ARTIFACT_DIR / "capa")
    ctx = RoleContext(role=Role.ORCHESTRATOR, task_id=args.task_id or "CAPA-CLI")

    if args.action == "create":
        record = store.create(
            finding=args.finding,
            root_cause=args.root_cause,
            corrective_action=args.corrective_action,
            preventive_action=args.preventive_action,
            verification_command=args.verification_command,
            linked_artifact=args.linked_artifact,
            linked_task_id=args.linked_task_id or args.task_id,
        )
        print(f"[qms] CAPA created: {record.id} ({record.closure_status})")
        print(f"  finding: {record.finding}")
        print(f"  root_cause: {record.root_cause}")
        print(f"  corrective_action: {record.corrective_action}")
        print(f"  preventive_action: {record.preventive_action}")
        print(f"  verification_command: {record.verification_command}")
    elif args.action == "close":
        record = store.close(args.nonconformance_id, args.status)
        print(f"[qms] CAPA {record.id} -> {record.closure_status}")
    elif args.action == "list":
        records = store.list_all()
        print(f"[qms] {len(records)} CAPA records, {store.open_count()} open")
        for rec in records:
            print(f"  - {rec.id} [{rec.closure_status}] {rec.finding[:70]}")
            if rec.linked_task_id:
                print(f"    task: {rec.linked_task_id}  artifact: {rec.linked_artifact}")
    elif args.action == "index":
        index_path = store.index_path
        if index_path.is_file():
            print(index_path.read_text(encoding="utf-8"))
        else:
            print("[qms] no CAPA index yet; run 'capa create' first")
    return 0


def cmd_accept(args: argparse.Namespace) -> int:
    if args.verdict != "REJECTED":
        print(
            "[qms] Gate 5 acceptance is blocked: this CLI has no verified QA evidence "
            "packet and will not treat --check-* declarations as evidence.",
            file=sys.stderr,
        )
        return 2

    ctx = RoleContext(role=Role.QA_A, task_id=args.task_id,
                      acceptance_targets={Path(args.artifact)})

    axiom_classification = []
    if args.axiom:
        for a in args.axiom:
            try:
                axiom_classification.append(_parse_axiom_spec(a))
            except ValueError as exc:
                print(f"[qms] {exc}", file=sys.stderr)
                return 2

    placeholder_findings = []
    if args.placeholder:
        for p in args.placeholder:
            parts = p.split(":", 4)
            if len(parts) < 4:
                print(f"[qms] invalid placeholder spec: {p!r} (expected file:line:token:context[:classified_as])", file=sys.stderr)
                return 2
            placeholder_findings.append({
                "file": parts[0],
                "line": int(parts[1]),
                "token": parts[2],
                "context": parts[3],
                "classified_as": parts[4] if len(parts) > 4 else "review",
            })

    remaining_debt = args.debt or []

    compliance = {
        "non_authoring_audit": _parse_bool(args.check_non_authoring_audit),
        "non_authoring_qa_rerun": _parse_bool(args.check_non_authoring_qa_rerun),
        "scope_labels_assigned": bool(args.status_tag),
        "owner_theorem_names_cited": _parse_bool(args.check_owner_theorem_names),
        "dag_hash_fresh": _parse_bool(args.check_dag_hash_fresh),
        "external_evidence_scoped": _parse_bool(args.check_external_evidence_scoped),
        "no_fake_closure_patterns": _parse_bool(args.check_no_fake_closure),
        "gaps_recorded_as_bucket3": _parse_bool(args.check_gaps_bucket3),
    }

    result = gate_5_acceptance(
        ctx,
        task_id=args.task_id,
        artifact_path=args.artifact,
        verdict=args.verdict,
        status_tags=args.status_tag or [],
        commands_run=args.commands_run or [],
        command_outputs=args.output or [],
        remaining_debt=remaining_debt,
        axiom_classification=axiom_classification,
        placeholder_findings=placeholder_findings,
        working_tree_scope=args.working_tree_scope,
        artifact_sha256=args.artifact_sha256,
        requires_capa=_parse_bool(args.requires_capa),
        capa_ids=args.capa_id or [],
        compliance_checklist=compliance,
    )

    for line in result.evidence:
        print(f"  + {line}")
    for f in result.findings:
        print(f"  ! {f}")
    print(f"[qms] gate-5 acceptance: {'passed' if result.passed else 'failed'} "
          f"(verdict={result.data.get('verdict', 'unknown')}, tag={result.status_tag})")
    return 0 if result.passed else 1


def cmd_quick_gate(args: argparse.Namespace) -> int:
    ctx = RoleContext(role=Role.QA_A, task_id=args.task_id or "QUICK-GATE")
    result = run_operator_quick_gate(ctx)
    for line in result.evidence:
        print(f"  + {line}")
    for finding in result.findings:
        print(f"  ! {finding}")
    print(f"[qms] operator quick gate: {'PASS' if result.passed else 'BLOCKED'}")
    return 0 if result.passed else 1


def cmd_capa_index(args: argparse.Namespace) -> int:
    store = CAPAStore(QMS_ARTIFACT_DIR / "capa")
    records = store.list_all()
    print(f"[qms] CAPA index: {len(records)} records, {store.open_count()} open")
    for rec in records:
        print(f"  - {rec.id} [{rec.closure_status}] {rec.finding}")
        print(f"    root_cause: {rec.root_cause}")
        print(f"    corrective_action: {rec.corrective_action}")
        print(f"    preventive_action: {rec.preventive_action}")
        print(f"    verification_command: {rec.verification_command}")
        print(f"    task: {rec.linked_task_id}  artifact: {rec.linked_artifact}")
        print(f"    created: {rec.created_at}  closed: {rec.closed_at}  verified: {rec.verified_at}")
    return 0


def cmd_run_all(args: argparse.Namespace) -> int:
    """Fail closed until role-separated orchestration has real evidence inputs."""
    print(
        "[qms] run-all is disabled: this CLI cannot establish independent "
        "owner search, generation review, audit, or QA evidence. Run gates "
        "individually and provide recorded evidence; no acceptance record was written.",
        file=sys.stderr,
    )
    return 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="QMS runner — Quality Management System per QMS-SOP-ALC-001"
    )
    parser.add_argument("--task-id", default="T-CLI", help="Task identifier (default: T-CLI)")
    sub = parser.add_subplots = parser.add_subparsers(dest="command", required=True)

    # intent
    p = sub.add_parser("intent", help="Gate 0: build formal intent envelope (G-A)")
    p.add_argument("--source-text", required=True, help="Source text or prompt excerpt")
    p.add_argument("--source-file", help="File to read as source_text")
    p.add_argument("--intake-classification", required=True,
                   choices=sorted(ie.INTAKE_CLASSIFICATIONS))
    p.add_argument("--classification", required=True)
    p.add_argument("--mathematical-domain", nargs="*", default=[])
    p.add_argument("--target-status", required=True, choices=sorted(ie.TARGET_STATUSES))
    p.add_argument("--risk-level", required=True, choices=sorted(ie.RISK_LEVELS))
    p.add_argument("--allowed-import", action="append", default=[])
    p.add_argument("--non-theorem-claim", action="append", default=[])
    p.add_argument("--formal-object", action="append", default=[])
    p.add_argument("--acceptance-theorem", action="append", default=[])
    p.add_argument("--scope-label", action="append", default=[], choices=sorted(ie.SCOPE_LABELS))
    p.add_argument("--source-path", action="append", default=[])
    p.add_argument("--out", type=Path, help="Output JSON path for the intent envelope")
    p.set_defaults(func=cmd_intent)

    # owner-search
    p = sub.add_parser("owner-search", help="Gate 1: owner-first search (G-A)")
    p.add_argument("--artifact", required=True)
    p.add_argument("--query", action="append", required=True,
                   help="Exact symbol or concept to search; repeat for multiple queries")
    p.add_argument("--search-lane", action="append", default=[])
    p.add_argument("--owner-file", action="append", default=[])
    p.add_argument("--existing-theorem-found", default="false")
    p.add_argument("--existing-theorem-name", default=None)
    p.add_argument("--missing-colimit-owner", default="false")
    p.add_argument("--bucket-3-obligation", default=None)
    p.set_defaults(func=cmd_owner_search)

    # generation
    p = sub.add_parser("generation", help="Gate 2: generation controls (G-A)")
    p.add_argument("--artifact", required=True)
    p.add_argument("--theorem-statement", default="")
    p.add_argument("--no-axiom", default="true")
    p.add_argument("--no-hidden-theorem-debt", default="true")
    p.add_argument("--no-prop-true", default="true")
    p.add_argument("--name-content-descriptive", default="true")
    p.add_argument("--no-broad-import", default="true")
    p.add_argument("--no-zorn-lie-ring", default="true")
    p.add_argument("--no-colimit-from-finite", default="true")
    p.add_argument("--no-quotient-collapse", default="true")
    p.add_argument("--sterile-imports", default="true")
    p.set_defaults(func=cmd_generation)

    # compile
    p = sub.add_parser("compile", help="Gate 3: sterile compile + independent audit (QA-A)")
    p.add_argument("--artifact", required=True)
    p.add_argument("--audit-report", help="Hash-matched independent A-A audit JSON")
    p.add_argument("--scope-label", default="open-debt", choices=sorted(ie.SCOPE_LABELS))
    p.add_argument("--countermodel-found", default="false")
    p.add_argument("--repair-split-required", default="false")
    p.set_defaults(func=cmd_compile)

    # capa
    p = sub.add_parser("capa", help="Gate 4: CAPA record management (Orchestrator)")
    p.add_argument("action", choices=["create", "close", "list", "index"])
    p.add_argument("--nonconformance-id", default=None)
    p.add_argument("--finding", default="")
    p.add_argument("--root-cause", default="")
    p.add_argument("--corrective-action", default="")
    p.add_argument("--preventive-action", default="")
    p.add_argument("--verification-command", default="")
    p.add_argument("--linked-artifact", default=None)
    p.add_argument("--linked-task-id", default=None)
    p.add_argument("--status", default="closed", choices=["open", "closed", "verified"])
    p.set_defaults(func=cmd_capa)

    # accept
    p = sub.add_parser("accept", help="Gate 5: blocked until verified QA evidence is available")
    p.add_argument("--artifact", required=True)
    p.add_argument("--verdict", required=True, choices=["ACCEPTED", "ACCEPTED_WITH_LIMITED_SCOPE", "REJECTED"])
    p.add_argument("--status-tag", action="append", default=[],
                   choices=sorted(qa.STATUS_TAGS))
    p.add_argument("--command", dest="commands_run", action="append", default=[])
    p.add_argument("--output", action="append", default=[])
    p.add_argument("--debt", action="append", default=[])
    p.add_argument("--axiom", action="append", default=[],
                   help="theorem:axiom:origin[:role[:approved]]")
    p.add_argument("--placeholder", action="append", default=[],
                   help="file:line:token:context[:classified_as]")
    p.add_argument("--working-tree-scope", default="clean",
                   choices=["clean", "dirty-with-excluded-artifacts", "dirty"])
    p.add_argument("--artifact-sha256", default=None)
    p.add_argument("--requires-capa", default="false")
    p.add_argument("--capa-id", action="append", default=[])
    p.add_argument("--check-non-authoring-audit", default="false")
    p.add_argument("--check-non-authoring-qa-rerun", default="false")
    p.add_argument("--check-owner-theorem-names", default="false")
    p.add_argument("--check-dag-hash-fresh", default="false")
    p.add_argument("--check-external-evidence-scoped", default="false")
    p.add_argument("--check-no-fake-closure", default="false")
    p.add_argument("--check-gaps-bucket3", default="false")
    p.set_defaults(func=cmd_accept)

    # quick-gate
    p = sub.add_parser("quick-gate", help="Operator quick gate (SOP section 18)")
    p.set_defaults(func=cmd_quick_gate)

    # capa-index
    p = sub.add_parser("capa-index", help="Show CAPA index")
    p.set_defaults(func=cmd_capa_index)

    # run-all
    p = sub.add_parser("run-all", help="Disabled until independent gate evidence can be supplied")
    p.set_defaults(func=cmd_run_all)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if not args.command:
        parser.print_help()
        return 2
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
