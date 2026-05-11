#!/usr/bin/env python3
"""Run a verification governance pulse for the Bee hive.

This command selects declaration candidates and executes
`run_unified_verification` with policy-aware lane merges.
"""

from __future__ import annotations

import argparse
import os
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    REPO_ROOT = Path(__file__).resolve().parents[2]
    if str(REPO_ROOT) not in sys.path:
        sys.path.insert(0, str(REPO_ROOT))
    from tools.infra.run_unified_verification import run as run_unified_verification
    from tools.infra.run_unified_verification import utc_run_id
    from tools.infra.build_changed_lean import changed_paths
    from tools.pathing import repo_root, resolve_decl_metadata_file
else:
    from . import run_unified_verification
    from .build_changed_lean import changed_paths
    from tools.pathing import repo_root, resolve_decl_metadata_file
try:
    from tools.infra import pilot_hardening_state as _pilot_hardening_state
    build_hardening_note_section = getattr(_pilot_hardening_state, "build_hardening_note_section", None)
except Exception:  # pragma: no cover - import path fallback
    _pilot_hardening_state = None
    build_hardening_note_section = None


DEFAULT_DECL_INDEX = resolve_decl_metadata_file()


def _resolve_summary_paths(argv: argparse.Namespace, *, run_md_out: Path) -> list[Path]:
    explicit = getattr(argv, "primary_summary_path", None)
    if explicit is None:
        explicit = os.environ.get("GITHUB_STEP_SUMMARY")
    if explicit is not None:
        if isinstance(explicit, Path):
            candidate = explicit
        else:
            candidate = Path(explicit)
        if not candidate.is_absolute():
            candidate = (repo_root() / candidate).resolve()
        return [candidate]
    return [run_md_out]


def _load_json(path: Path | None) -> dict[str, Any]:
    if path is None or not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return payload if isinstance(payload, dict) else {}


def _append_hardening_note(summary_paths: list[Path], payload_path: Path | None) -> None:
    if not summary_paths:
        return
    payload = _load_json(payload_path)
    if not payload:
        return
    if build_hardening_note_section is None:
        return
    section = build_hardening_note_section(payload)
    if not section:
        return
    note = "\n".join(section) + "\n"
    for summary_path in summary_paths:
        summary_path.parent.mkdir(parents=True, exist_ok=True)
        with summary_path.open("a", encoding="utf-8") as handle:
            handle.write(note)


def _append_hardening_note_payload(summary_paths: list[Path], payload: dict[str, Any]) -> None:
    if not summary_paths or not payload:
        return
    if build_hardening_note_section is None:
        return
    section = build_hardening_note_section(payload)
    if not section:
        return
    note = "\n".join(section) + "\n"
    for summary_path in summary_paths:
        summary_path.parent.mkdir(parents=True, exist_ok=True)
        with summary_path.open("a", encoding="utf-8") as handle:
            handle.write(note)


def _build_placeholder_signal_section(payload: dict[str, Any]) -> list[str]:
    if payload.get("schema") != "info_geometry.placeholder_audit_signals.v1":
        return []
    signals = payload.get("signals")
    if not isinstance(signals, list):
        return []

    summary = payload.get("summary")
    if not isinstance(summary, dict):
        summary = {}

    total = summary.get("signal_count", len(signals))
    auto_count = summary.get("autoproof_signal_count", 0)
    debt_count = summary.get("closure_debt_signal_count", 0)

    lines: list[str] = []
    lines.append("## Placeholder Trust Signals")
    lines.append(f"- signal_count: **{total}**")
    lines.append(f"- autoproof_signals: **{auto_count}**")
    lines.append(f"- closure_debt_signals: **{debt_count}**")

    if total == 0:
        lines.append("- status: clean")
        return lines

    lines.append("- signals:")
    for item in signals[:20]:
        if not isinstance(item, dict):
            continue
        decl_ref = item.get("decl_ref") or item.get("declaration_name") or "<unknown>"
        signal = item.get("signal") or "<no-signal>"
        task_hint = item.get("task_hint") or ""
        severity = item.get("severity") or ""
        file = item.get("file") or ""
        line = item.get("line", "")
        line_label = f"{file}:{line}" if file else ""
        suffix = ""
        if task_hint:
            suffix = f" task={task_hint}"
        if severity:
            suffix = f"{suffix} ({severity})"
        if line_label:
            suffix = f"{suffix} @{line_label}"
        lines.append(f"- `{decl_ref}` {signal}{suffix}")

    return lines


def _append_placeholder_signal_payload(summary_paths: list[Path], payload: dict[str, Any]) -> None:
    if not summary_paths:
        return
    section = _build_placeholder_signal_section(payload)
    if not section:
        return
    note = "\n".join(section) + "\n"
    for summary_path in summary_paths:
        summary_path.parent.mkdir(parents=True, exist_ok=True)
        with summary_path.open("a", encoding="utf-8") as handle:
            handle.write(note)


def _append_placeholder_signal_note(summary_paths: list[Path], payload_path: Path | None) -> None:
    if payload_path is None:
        return
    payload = _load_json(payload_path)
    if not payload:
        return
    _append_placeholder_signal_payload(summary_paths=summary_paths, payload=payload)


def _apply_pilot_hardening_update(
    argv: argparse.Namespace,
    *,
    run_id: str,
    run_exit_code: int,
    report_path: Path,
    summary_paths: list[Path],
) -> None:
    state_path = getattr(argv, "pilot_state", None)
    if state_path is None or _pilot_hardening_state is None:
        return

    update_payload = (
        Path(argv.pilot_hardening_json)
        if getattr(argv, "pilot_hardening_json", None)
        else None
    )
    update_args = argparse.Namespace(
        state=Path(state_path),
        hard_policy_path=getattr(argv, "pilot_hard_policy_path", "tools/infra/verification_policy_pilot_hard.yaml"),
        soft_policy_path=getattr(argv, "pilot_soft_policy_path", "tools/infra/verification_policy_pilot.yaml"),
        hard_mode_threshold=int(getattr(argv, "pilot_hard_mode_threshold", 4)),
        force_hard=str(getattr(argv, "pilot_force_hard", "false")),
        action="update",
        pilot_report=str(report_path),
        run_id=run_id,
        exit_code=run_exit_code,
        max_history=int(getattr(argv, "pilot_max_history", 20)),
        github_output=Path(argv.pilot_github_output) if getattr(argv, "pilot_github_output", None) else None,
        json_out=update_payload,
        markdown_out=None,
    )
    payload = _pilot_hardening_state.action_update(update_args)
    _append_hardening_note_payload(summary_paths=summary_paths, payload=payload)


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    out: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            raw = raw.strip()
            if not raw:
                continue
            try:
                payload = json.loads(raw)
            except Exception:
                continue
            if isinstance(payload, dict):
                out.append(payload)
    return out


def _normalize_path(path: str | Path, root: Path) -> Path:
    value = Path(path)
    if value.is_absolute():
        return value.resolve()
    return (root / value).resolve()


def _changed_has(row_path: Path, changed_files: set[Path]) -> bool:
    candidate = row_path.resolve()
    if candidate in changed_files:
        return True
    return any(
        changed.resolve().parent == candidate.parent and changed.resolve().name == candidate.name
        for changed in changed_files
    )


def _collect_candidate_decl_rows(
    *,
    decl_index: Path,
    scope: str,
    changed_files: set[Path] | None,
    declaration_prefix: list[str],
    max_rows: int | None,
    root: Path,
) -> list[dict[str, Any]]:
    rows = _read_jsonl(decl_index)
    if not rows:
        return []

    changed_files = set(changed_files or set())
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    max_rows = max_rows if (max_rows is not None and max_rows > 0) else None

    for row in rows:
        name = str(row.get("name") or "").strip()
        if not name:
            continue

        if declaration_prefix and not any(name.startswith(prefix) for prefix in declaration_prefix):
            continue

        if scope == "changed":
            file_value = str(row.get("file") or "").strip()
            if not file_value:
                continue
            if not changed_files:
                continue
            file_path = _normalize_path(file_value, root)
            if not _changed_has(file_path, changed_files):
                continue

        if name in seen:
            continue

        seen.add(name)
        out.append(
            {
                "decl": name,
                "module": str(row.get("module") or ""),
                "kind": str(row.get("kind") or ""),
            }
        )
        if max_rows is not None and len(out) >= max_rows:
            break

    return out


def _write_decl_payload(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")


def _write_empty_pulse_reports(
    *,
    json_out: Path,
    md_out: Path | None,
    run_id: str,
    scope: str,
    target_class: str,
) -> None:
    json_out.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "summary": {
            "target_class": target_class,
            "scope": scope,
            "total_declarations": 0,
            "failed_hard": 0,
            "failed_soft": 0,
            "failed": 0,
        },
        "declarations": [],
        "policy": {
            "target_class": target_class,
        },
        "lane_health": {},
        "lane_metrics": {},
        "run_id": run_id,
        "contract_artifacts": [],
    }
    json_out.write_text(json.dumps(payload, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    if md_out is not None:
        md_out.write_text(
            "\n".join(
                [
                    "# Superorganism Pulse (No Declarations)",
                    f"- run id: {run_id}",
                    f"- scope: {scope}",
                    f"- target class: {target_class}",
                    "- status: clean",
                ]
            )
            + "\n",
            encoding="utf-8",
        )


def run_pulse(argv: argparse.Namespace) -> int:
    root = repo_root()
    if argv.scope == "changed":
        changed_files = {
            p.resolve()
            for p in changed_paths(
                root, include_untracked=argv.include_untracked, base_ref=argv.base_ref
            )
            if p.suffix == ".lean"
        }
    else:
        changed_files = set()

    rows = _collect_candidate_decl_rows(
        decl_index=argv.decl_index,
        scope=argv.scope,
        changed_files=changed_files,
        declaration_prefix=argv.decl_prefix,
        max_rows=argv.max_rows,
        root=root,
    )

    output_root = Path(argv.output_root)
    if not output_root.is_absolute():
        output_root = (root / output_root).resolve()
    output_root.mkdir(parents=True, exist_ok=True)

    if __package__ in (None, ""):
        run_id = argv.run_id or utc_run_id()
    else:
        run_id = argv.run_id or run_unified_verification.utc_run_id()
    run_dir = output_root / run_id
    target_class = argv.target_class or "default"
    run_json_out = Path(argv.json_out) if argv.json_out else run_dir / "unified.json"
    run_md_out = Path(argv.md_out) if argv.md_out else run_dir / "summary.md"
    summary_paths = _resolve_summary_paths(argv, run_md_out=run_md_out)
    decl_path = run_dir / "decls.jsonl"

    if not rows:
        print("[superorganism] no declarations selected for verification pulse")
        _write_empty_pulse_reports(
            json_out=run_json_out,
            md_out=run_md_out,
            run_id=run_id,
            scope=argv.scope,
            target_class=target_class,
        )
        _apply_pilot_hardening_update(
            argv,
            run_id=run_id,
            run_exit_code=0,
            report_path=run_json_out,
            summary_paths=summary_paths,
        )
        _append_placeholder_signal_note(
            summary_paths=summary_paths,
            payload_path=getattr(argv, "placeholder_signal_report", None),
        )
        return 0

    _write_decl_payload(decl_path, rows)

    mathfulness_json = argv.mathfulness_json
    if mathfulness_json is not None:
        mathfulness_json = Path(mathfulness_json)
        if not mathfulness_json.is_absolute():
            mathfulness_json = (root / mathfulness_json).resolve()
        if not mathfulness_json.exists():
            mathfulness_json = None

    if argv.auto_mathfulness and mathfulness_json is None:
        candidate = root / "reports" / "dag" / "mathfulness-audit.json"
        if candidate.exists():
            mathfulness_json = candidate

    unified = argparse.Namespace(
        decls=[decl_path],
        leanparanoia_jsonl=Path(argv.leanparanoia_jsonl) if argv.leanparanoia_jsonl else None,
        safeverify_jsonl=Path(argv.safeverify_jsonl) if argv.safeverify_jsonl else None,
        kernel_jsonl=Path(argv.kernel_jsonl) if argv.kernel_jsonl else None,
        autograder_jsonl=Path(argv.autograder_jsonl) if argv.autograder_jsonl else None,
        promotion_json=Path(argv.promotion_json) if argv.promotion_json else None,
        mathfulness_json=mathfulness_json,
        rethlas_json=Path(argv.rethlas_json) if argv.rethlas_json else None,
        conductivity_json=Path(argv.conductivity_json) if argv.conductivity_json else None,
        socratic_json=Path(argv.socratic_json) if argv.socratic_json else None,
        paperclip_json=Path(argv.paperclip_json) if argv.paperclip_json else None,
        llm_audit_json=Path(argv.llm_audit_json) if getattr(argv, "llm_audit_json", None) else None,
        policy=Path(argv.policy) if argv.policy else None,
        target_class=argv.target_class,
        output_root=output_root,
        run_id=run_id,
        no_lane_wrappers=argv.no_lane_wrappers,
        json_out=run_json_out,
        md_out=run_md_out,
    )

    print(
        f"[superorganism] selected {len(rows)} declarations",
        f"scope={argv.scope}",
        f"target_class={argv.target_class or 'default'}",
        f"run_id={run_id}",
    )

    if __package__ in (None, ""):
        rc = run_unified_verification(unified)
    else:
        rc = run_unified_verification.run(unified)

    _apply_pilot_hardening_update(
        argv,
        run_id=run_id,
        run_exit_code=rc,
        report_path=run_json_out,
        summary_paths=summary_paths,
    )
    _append_placeholder_signal_note(
        summary_paths=summary_paths,
        payload_path=getattr(argv, "placeholder_signal_report", None),
    )
    if not getattr(argv, "pilot_state", None) and getattr(argv, "pilot_hardening_payload", None):
        _append_hardening_note(
            summary_paths=summary_paths,
            payload_path=Path(argv.pilot_hardening_payload),
        )
    return rc


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope", choices=["changed", "all"], default="changed", help="Declaration scope")
    parser.add_argument("--decl-index", type=Path, default=DEFAULT_DECL_INDEX, help="Declaration metadata JSONL")
    parser.add_argument("--decl-prefix", action="append", default=[], help="Filter declarations by full-name prefix")
    parser.add_argument("--max-rows", type=int, default=0, help="Limit selected declaration rows (0 means no limit)")
    parser.add_argument("--include-untracked", action="store_true", default=False)
    parser.add_argument(
        "--base-ref",
        default=None,
        help=(
            "Optional git base ref to compare against changed files. "
            "When set, uses this ref (or its merge-base with HEAD) as baseline."
        ),
    )
    parser.add_argument("--mathfulness-json", type=Path, help="Optional mathfulness-audit JSON to enable semantic lane")
    parser.add_argument(
        "--auto-mathfulness", action="store_true", default=False, help="Auto-load reports/dag/mathfulness-audit.json if present"
    )
    parser.add_argument("--leanparanoia-jsonl", type=Path, help="LeanParanoia bridge artifact")
    parser.add_argument("--safeverify-jsonl", type=Path, help="SafeVerify bridge artifact")
    parser.add_argument("--kernel-jsonl", type=Path, help="Lean verification packet artifact")
    parser.add_argument("--autograder-jsonl", type=Path, help="Lean autograder artifact")
    parser.add_argument("--rethlas-json", type=Path, help="Rethlas artifact")
    parser.add_argument("--conductivity-json", type=Path, help="Lean conductivity artifact (representation-depth)")
    parser.add_argument("--socratic-json", type=Path, help="SocraticQuestionPacket/Socratic artifact (JSON/JSONL)")
    parser.add_argument("--paperclip-json", type=Path, help="Paperclip control/event artifact (JSON/JSONL)")
    parser.add_argument("--promotion-json", type=Path, help="Promotion artifact")
    parser.add_argument("--llm-audit-json", type=Path, help="LLM closure debt audit JSON/JSONL")
    parser.add_argument("--policy", type=Path, help="Path to verification policy")
    parser.add_argument("--target-class", choices=["L0", "L1", "L2", "l0", "l1", "l2"], default=None)
    parser.add_argument("--output-root", type=Path, default=Path("reports") / "verification")
    parser.add_argument("--run-id", type=str, default="")
    parser.add_argument("--json-out", type=Path, help="Write unified JSON report to this path")
    parser.add_argument("--md-out", type=Path, help="Write unified markdown report to this path")
    parser.add_argument(
        "--primary-summary-path",
        type=Path,
        default=None,
        help="Optional canonical summary destination for hardening note (for example $GITHUB_STEP_SUMMARY).",
    )
    parser.add_argument(
        "--pilot-hardening-payload",
        type=Path,
        help="Optional pilot hardening payload JSON; append hard-mode progression note into summary.md.",
    )
    parser.add_argument(
        "--pilot-state",
        type=Path,
        help="Optional hardening state file; when set, refresh hard-mode state and write hardening note.",
    )
    parser.add_argument(
        "--pilot-hard-mode-threshold",
        type=int,
        default=4,
        help="Pilot hardening threshold used when updating hardening state.",
    )
    parser.add_argument(
        "--pilot-force-hard",
        default="false",
        help="Override state and force hard mode for pilot hardening state updates.",
    )
    parser.add_argument(
        "--pilot-max-history",
        type=int,
        default=20,
        help="Pilot hardening state history window size.",
    )
    parser.add_argument("--pilot-hard-policy-path", default="tools/infra/verification_policy_pilot_hard.yaml")
    parser.add_argument("--pilot-soft-policy-path", default="tools/infra/verification_policy_pilot.yaml")
    parser.add_argument(
        "--pilot-hardening-json",
        type=Path,
        help="Optional JSON payload path for pilot hardening state update output.",
    )
    parser.add_argument(
        "--placeholder-signal-report",
        type=Path,
        help="Optional placeholder trust signal JSON; append a placeholder-signal summary into summary output.",
    )
    parser.add_argument("--pilot-github-output", type=Path, help="Optional GitHub output file for hardening state action.")
    parser.add_argument("--no-lane-wrappers", action="store_true", help="Pass contract rows directly")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    return run_pulse(args)


if __name__ == "__main__":
    raise SystemExit(main())
