#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]

BLOCKING_STATES = {
    "context_built",
    "patch_proposed",
    "verified",
    "audit_clean",
    "promotion_ready",
    "promoted",
    "done",
    "completed",
    "complete",
    "blocked",
    "quarantined",
}

STATE_ALIASES = {
    "verify": "verified",
    "verified_done": "verified",
    "audit-clean": "audit_clean",
    "promotion-ready": "promotion_ready",
    "promote": "promoted",
    "complete": "completed",
}

INSUFFICIENT_EVIDENCE_HINTS = {
    "agent said done",
    "subagent done",
    "llm summary",
    "kanban comment",
    "graph proximity",
    "semantic similarity",
    "retrieval context only",
    "diagnostic score",
    "hodge diagnostic",
    "drazin diagnostic",
    "lightcone diagnostic",
    "arango neighborhood",
}

POLICY = {
    "schema": "info_geometry.kanban_evidence_lint.policy.v1",
    "doctrine": (
        "Kanban done means a workflow artifact was delivered; it does not mean "
        "a theorem was admitted, promoted, or mathematically true."
    ),
    "authority_boundary": (
        "Hermes/Kanban coordinates work. Hive packets record workflow lineage. "
        "Arango ranks and navigates. Lean/build/audit/promotion evidence carries "
        "admission authority."
    ),
    "insufficient_evidence": sorted(INSUFFICIENT_EVIDENCE_HINTS),
    "advanced_states_checked": sorted(BLOCKING_STATES),
}


@dataclass(frozen=True)
class Finding:
    task_id: str
    state: str
    severity: str
    reason: str
    missing: list[str]
    authority_level: str | None
    recommended_action: str


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except Exception:
        return path.as_posix()


def load_json_or_jsonl(path: Path) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8")
    stripped = text.strip()
    if not stripped:
        return []
    if stripped[0] in "[{":
        try:
            payload = json.loads(stripped)
            return normalize_payload(payload)
        except json.JSONDecodeError as exc:
            if stripped[0] == "[":
                raise SystemExit(f"{path}: invalid JSON array/object input: {exc}") from exc
            # A JSONL file commonly starts with `{`.  If whole-file parsing
            # reports extra data, fall through to row-by-row JSONL parsing.
            if "Extra data" not in str(exc):
                raise SystemExit(f"{path}: invalid JSON object input: {exc}") from exc
    rows: list[dict[str, Any]] = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        raw = raw.strip()
        if not raw:
            continue
        try:
            row = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"{path}:{lineno}: invalid JSONL row: {exc}") from exc
        if isinstance(row, dict):
            rows.append(row)
        else:
            rows.append({"task_id": f"{path.name}:{lineno}", "payload": row})
    return rows


def normalize_payload(payload: Any) -> list[dict[str, Any]]:
    if isinstance(payload, list):
        return [row if isinstance(row, dict) else {"payload": row} for row in payload]
    if isinstance(payload, dict):
        for key in ("tasks", "items", "rows", "packets", "results"):
            value = payload.get(key)
            if isinstance(value, list):
                return [row if isinstance(row, dict) else {"payload": row} for row in value]
        return [payload]
    return [{"payload": payload}]


def nonempty(value: Any) -> bool:
    if value is None:
        return False
    if value is False:
        return False
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, tuple, set, dict)):
        return bool(value)
    return True


def produced(task: dict[str, Any]) -> dict[str, Any]:
    artifacts = task.get("produced_artifacts")
    if isinstance(artifacts, dict):
        return artifacts
    artifacts = task.get("artifacts")
    if isinstance(artifacts, dict):
        return artifacts
    return {}


def value_at(task: dict[str, Any], *keys: str) -> Any:
    artifacts = produced(task)
    for key in keys:
        if nonempty(task.get(key)):
            return task.get(key)
        if nonempty(artifacts.get(key)):
            return artifacts.get(key)
    return None


def has_any(task: dict[str, Any], *keys: str) -> bool:
    return any(nonempty(value_at(task, key)) for key in keys)


def has_any_list(task: dict[str, Any], groups: list[tuple[str, ...]]) -> bool:
    return any(has_any(task, *group) for group in groups)


def normalize_state(task: dict[str, Any]) -> str:
    raw = (
        task.get("state")
        or task.get("status")
        or task.get("kanban_state")
        or task.get("workflow_state")
        or ""
    )
    state = str(raw).strip().lower().replace(" ", "_")
    return STATE_ALIASES.get(state, state)


def task_id(task: dict[str, Any], fallback: str) -> str:
    for key in ("task_id", "_key", "id", "key", "finding_key"):
        value = task.get(key)
        if nonempty(value):
            return str(value)
    return fallback


def authority_level(task: dict[str, Any]) -> str | None:
    value = task.get("authority_level") or task.get("authority")
    return str(value) if nonempty(value) else None


def has_context_evidence(task: dict[str, Any]) -> bool:
    return has_any_list(
        task,
        [
            ("retrieval_packet", "retrieval_packets", "retrieval_packet_id"),
            ("context_packet", "context_packets", "context_packet_id"),
            ("report", "reports", "report_path", "report_paths"),
            ("arango_packet", "arango_packets", "arango_packet_id"),
            ("hive_packet", "hive_packets", "hive_packet_id"),
            ("source_excerpt", "source_anchor", "claim_surface"),
        ],
    )


def has_patch_evidence(task: dict[str, Any]) -> bool:
    return has_any_list(
        task,
        [
            ("commit", "commit_hash"),
            ("diff", "diff_path", "patch", "patch_path"),
            ("branch", "pr", "pull_request"),
            ("source_path", "path", "file"),
        ],
    )


def has_build_evidence(task: dict[str, Any]) -> bool:
    return has_any_list(
        task,
        [
            ("build_log", "build_log_path", "build_result"),
            ("lean_owner", "lean_module", "target_decl"),
            ("checked_certificate", "certificate", "certificate_path"),
            ("verification_packet", "verification_packets", "verification_packet_id"),
            ("command", "build_command", "test_command"),
            ("result", "exit_code"),
        ],
    )


def has_audit_evidence(task: dict[str, Any]) -> bool:
    return has_any_list(
        task,
        [
            ("audit_report", "audit_reports", "audit_report_path"),
            ("semantic_audit", "semantic_audit_report"),
            ("mathfulness_audit", "mathfulness_audit_report"),
            ("quarantine_audit", "quarantine_audit_report"),
            ("pauli_audit", "pauli_audit_report"),
            ("audit_packet", "audit_packets", "audit_packet_id"),
        ],
    )


def has_promotion_evidence(task: dict[str, Any]) -> bool:
    return has_any_list(
        task,
        [
            ("promotion_decision", "promotion_decision_packet"),
            ("promotion_packet", "promotion_packets", "promotion_packet_id"),
            ("hold_decision", "quarantine_decision"),
        ],
    )


def has_blocker_evidence(task: dict[str, Any]) -> bool:
    return has_any(
        task,
        "blocked_reason",
        "blocker",
        "blockers",
        "failure",
        "failure_log",
        "finding_key",
        "source_excerpt",
        "path",
        "file",
    )


def has_quarantine_evidence(task: dict[str, Any]) -> bool:
    has_reason = has_any(task, "quarantine_reason", "manifest_reason", "blocked_reason")
    has_source = has_any(task, "source_excerpt", "path", "file", "line", "finding_key")
    has_exit = has_any(task, "exit_path", "recommended_action", "repair_route")
    return has_reason and has_source and has_exit


def negative_hint_text(task: dict[str, Any]) -> str:
    parts: list[str] = []
    for key in ("comment", "comments", "summary", "notes", "evidence", "evidence_text"):
        value = task.get(key)
        if nonempty(value):
            parts.append(json.dumps(value, ensure_ascii=False) if not isinstance(value, str) else value)
    artifacts = produced(task)
    for key in ("comment", "comments", "summary", "notes", "evidence", "evidence_text"):
        value = artifacts.get(key)
        if nonempty(value):
            parts.append(json.dumps(value, ensure_ascii=False) if not isinstance(value, str) else value)
    return "\n".join(parts).lower()


def missing_finding(
    task: dict[str, Any],
    *,
    fallback_id: str,
    state: str,
    reason: str,
    missing: list[str],
    action: str,
    severity: str = "blocking",
) -> Finding:
    return Finding(
        task_id=task_id(task, fallback_id),
        state=state,
        severity=severity,
        reason=reason,
        missing=missing,
        authority_level=authority_level(task),
        recommended_action=action,
    )


def lint_task(task: dict[str, Any], fallback_id: str) -> list[Finding]:
    state = normalize_state(task)
    if state not in BLOCKING_STATES:
        return []

    findings: list[Finding] = []

    if state == "context_built" and not has_context_evidence(task):
        findings.append(
            missing_finding(
                task,
                fallback_id=fallback_id,
                state=state,
                reason="context_built requires a retrieval/report/context packet pointer",
                missing=["retrieval_packet", "context_packet", "report", "arango_packet"],
                action="attach context/retrieval/report evidence or downgrade task state",
            )
        )

    if state == "patch_proposed" and not has_patch_evidence(task):
        findings.append(
            missing_finding(
                task,
                fallback_id=fallback_id,
                state=state,
                reason="patch_proposed requires a diff, branch, commit, PR, or source path",
                missing=["diff", "branch", "commit", "source_path"],
                action="attach patch/source evidence or downgrade task state",
            )
        )

    if state in {"verified", "done", "completed", "complete"} and not has_build_evidence(task):
        findings.append(
            missing_finding(
                task,
                fallback_id=fallback_id,
                state=state,
                reason="verified/done states require Lean/build/test evidence",
                missing=["build_log", "checked_certificate", "verification_packet", "build_command"],
                action="attach Lean/build verification evidence or downgrade task state",
            )
        )

    if state == "audit_clean" and not has_audit_evidence(task):
        findings.append(
            missing_finding(
                task,
                fallback_id=fallback_id,
                state=state,
                reason="audit_clean requires an audit report or audit packet",
                missing=["audit_report", "audit_packet"],
                action="attach mathfulness/semantic/quarantine/Pauli audit evidence or downgrade task state",
            )
        )

    if state == "promotion_ready":
        missing: list[str] = []
        if not has_build_evidence(task):
            missing.append("build_checked")
        if not has_audit_evidence(task):
            missing.append("audit_checked")
        if missing:
            findings.append(
                missing_finding(
                    task,
                    fallback_id=fallback_id,
                    state=state,
                    reason="promotion_ready requires both build evidence and audit evidence",
                    missing=missing,
                    action="attach build and audit evidence or downgrade task state",
                )
            )

    if state == "promoted" and not has_promotion_evidence(task):
        findings.append(
            missing_finding(
                task,
                fallback_id=fallback_id,
                state=state,
                reason="promoted requires a promotion decision packet",
                missing=["promotion_decision_packet"],
                action="attach promotion/hold decision packet or downgrade task state",
            )
        )

    if state == "blocked" and not has_blocker_evidence(task):
        findings.append(
            missing_finding(
                task,
                fallback_id=fallback_id,
                state=state,
                reason="blocked requires an exact blocker pointer",
                missing=["blocked_reason", "failure_log", "source_location", "finding_key"],
                action="attach exact blocker evidence or downgrade task state",
            )
        )

    if state == "quarantined" and not has_quarantine_evidence(task):
        findings.append(
            missing_finding(
                task,
                fallback_id=fallback_id,
                state=state,
                reason="quarantined requires reason, source evidence, and exit path",
                missing=["quarantine_reason", "source_evidence", "exit_path"],
                action="attach quarantine reason/source/exit evidence or downgrade task state",
            )
        )

    hint_text = negative_hint_text(task)
    bad_hints = sorted(hint for hint in INSUFFICIENT_EVIDENCE_HINTS if hint in hint_text)
    if bad_hints and state in {"verified", "audit_clean", "promotion_ready", "promoted", "done", "completed"}:
        findings.append(
            missing_finding(
                task,
                fallback_id=fallback_id,
                state=state,
                severity="review",
                reason="task cites evidence forms that are explicitly insufficient for proof/admission authority",
                missing=bad_hints,
                action="replace comments/diagnostics with concrete Lean/build/audit/promotion evidence",
            )
        )

    return findings


def build_report(inputs: list[Path]) -> dict[str, Any]:
    tasks: list[dict[str, Any]] = []
    input_rows: list[dict[str, Any]] = []
    for path in inputs:
        rows = load_json_or_jsonl(path)
        input_rows.append({"path": rel(path), "task_count": len(rows)})
        for index, row in enumerate(rows, start=1):
            row = dict(row)
            row.setdefault("_input_path", rel(path))
            row.setdefault("_input_index", index)
            tasks.append(row)

    findings: list[Finding] = []
    for index, task in enumerate(tasks, start=1):
        fallback = f"task:{index}"
        findings.extend(lint_task(task, fallback))

    state_counts = Counter(normalize_state(task) or "unknown" for task in tasks)
    severity_counts = Counter(f.severity for f in findings)
    blocking_count = severity_counts.get("blocking", 0)

    return {
        "schema": "info_geometry.kanban_evidence_lint.report.v1",
        "policy": POLICY,
        "inputs": {
            "files": input_rows,
            "task_count": len(tasks),
        },
        "summary": {
            "task_count": len(tasks),
            "finding_count": len(findings),
            "blocking_finding_count": blocking_count,
            "review_finding_count": severity_counts.get("review", 0),
            "state_counts": dict(sorted(state_counts.items())),
            "severity_counts": dict(sorted(severity_counts.items())),
        },
        "findings": [asdict(finding) for finding in findings],
    }


def render_markdown(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# Kanban Evidence Lint",
        "",
        "Kanban state is workflow coordination, not proof authority.",
        "",
        "## Summary",
        "",
        f"- Tasks scanned: {summary['task_count']}",
        f"- Findings: {summary['finding_count']}",
        f"- Blocking findings: {summary['blocking_finding_count']}",
        f"- Review findings: {summary['review_finding_count']}",
        "",
        "## State counts",
        "",
    ]
    for state, count in summary["state_counts"].items():
        lines.append(f"- `{state}`: {count}")
    lines.extend(["", "## Findings", ""])
    findings = report["findings"]
    if not findings:
        lines.append("No evidence-inflation findings.")
    else:
        for finding in findings:
            lines.extend(
                [
                    f"### {finding['severity']}: {finding['task_id']}",
                    "",
                    f"- State: `{finding['state']}`",
                    f"- Reason: {finding['reason']}",
                    f"- Missing: {', '.join(f'`{item}`' for item in finding['missing'])}",
                    f"- Authority level: `{finding.get('authority_level')}`",
                    f"- Recommended action: {finding['recommended_action']}",
                    "",
                ]
            )
    lines.extend(
        [
            "## Doctrine",
            "",
            "- Kanban comments are not proof.",
            "- Subagent summaries are not proof.",
            "- Graph proximity is not proof.",
            "- Diagnostics are not proof.",
            "- Lean/build/audit/promotion evidence is required for admission states.",
            "",
        ]
    )
    return "\n".join(lines)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Lint Hermes/Kanban/Hive tasks for evidence-backed workflow states."
    )
    parser.add_argument("--input", action="append", required=True, help="Task JSON or JSONL input.")
    parser.add_argument("--json-out", help="Write JSON report.")
    parser.add_argument("--md-out", help="Write Markdown report.")
    parser.add_argument("--gate", action="store_true", help="Fail on blocking evidence findings.")
    args = parser.parse_args(argv)

    inputs = [Path(path) if Path(path).is_absolute() else ROOT / path for path in args.input]
    missing_inputs = [path for path in inputs if not path.exists()]
    if missing_inputs:
        for path in missing_inputs:
            print(f"missing input: {rel(path)}", file=sys.stderr)
        return 1

    report = build_report(inputs)

    if args.json_out:
        out = Path(args.json_out)
        if not out.is_absolute():
            out = ROOT / out
        write_text(out, json.dumps(report, indent=2, sort_keys=True) + "\n")

    if args.md_out:
        out = Path(args.md_out)
        if not out.is_absolute():
            out = ROOT / out
        write_text(out, render_markdown(report))

    if not args.json_out and not args.md_out:
        print(json.dumps(report, indent=2, sort_keys=True))

    if args.gate and report["summary"]["blocking_finding_count"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
