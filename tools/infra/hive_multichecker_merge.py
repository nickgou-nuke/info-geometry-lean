#!/usr/bin/env python3
"""Merge Hive checker telemetry into one declaration-oriented report.

This borrows the useful LeanDepViz idea of a unified multi-checker table while
keeping this repo's trust boundary intact: Lean remains proof authority, and the
merged report is audit/navigation telemetry rather than a proof certificate.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.hive_multichecker_report.v1"

DECL_KEYS = (
    "decl",
    "declaration",
    "declaration_name",
    "name",
    "fullName",
    "full_name",
    "theorem",
    "target_decl",
    "target_name",
    "problem",
)


ToolResult = dict[str, Any]


def iter_jsonl(path: Path | None) -> Iterable[dict[str, Any]]:
    if path is None or not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                yield row


def load_json_docs(path: Path | None) -> list[dict[str, Any]]:
    if path is None or not path.exists():
        return []
    if path.suffix.lower() == ".jsonl":
        return list(iter_jsonl(path))
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if isinstance(payload, list):
        return [row for row in payload if isinstance(row, dict)]
    if isinstance(payload, dict):
        return [payload]
    return []


def first_string(row: dict[str, Any], keys: tuple[str, ...] = DECL_KEYS) -> str | None:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return None


def nested_string(row: dict[str, Any], path: tuple[str, ...]) -> str | None:
    value: Any = row
    for key in path:
        if not isinstance(value, dict):
            return None
        value = value.get(key)
    return value if isinstance(value, str) and value else None


def decl_of(row: dict[str, Any], *, fallback: str | None = None) -> str | None:
    direct = first_string(row)
    if direct:
        return direct
    for path in (
        ("target_info", "name"),
        ("solution_info", "name"),
        ("targetInfo", "name"),
        ("solutionInfo", "name"),
        ("target_info", "constInfo", "name"),
        ("solution_info", "constInfo", "name"),
        ("targetInfo", "constInfo", "name"),
        ("solutionInfo", "constInfo", "name"),
    ):
        found = nested_string(row, path)
        if found:
            return found
    return fallback


def module_of(row: dict[str, Any]) -> str:
    value = row.get("module") or row.get("moduleName") or row.get("module_name")
    return str(value or "")


def kind_of(row: dict[str, Any]) -> str:
    value = row.get("kind") or row.get("constCategory") or row.get("target_kind") or row.get("targetKind")
    return str(value or "")


def message_list(value: Any) -> list[str]:
    if value is None or value is False:
        return []
    if isinstance(value, str):
        return [value] if value else []
    if isinstance(value, list):
        return [str(item) for item in value if item]
    if isinstance(value, dict):
        rows: list[str] = []
        for key, item in value.items():
            for msg in message_list(item):
                rows.append(f"{key}: {msg}")
        return rows
    return [str(value)]


def add_tool(table: dict[str, dict[str, Any]], decl: str, tool: str, result: ToolResult, *, module: str = "", kind: str = "") -> None:
    entry = table.setdefault(
        decl,
        {
            "decl": decl,
            "module": module,
            "kind": kind,
            "tools": {},
            "score": {"earned": 0.0, "total": 0.0},
        },
    )
    if module and not entry.get("module"):
        entry["module"] = module
    if kind and not entry.get("kind"):
        entry["kind"] = kind
    entry["tools"][tool] = result
    score = result.get("score")
    if isinstance(score, dict):
        entry["score"]["earned"] += float(score.get("earned") or 0)
        entry["score"]["total"] += float(score.get("total") or 0)


def load_declarations(paths: list[Path]) -> dict[str, dict[str, Any]]:
    table: dict[str, dict[str, Any]] = {}
    for path in paths:
        for row in load_json_docs(path):
            decl = decl_of(row)
            if not decl:
                continue
            table.setdefault(
                decl,
                {
                    "decl": decl,
                    "module": module_of(row),
                    "kind": kind_of(row),
                    "tools": {},
                    "score": {"earned": 0.0, "total": 0.0},
                },
            )
    return table


def leanparanoia_result(row: dict[str, Any]) -> ToolResult:
    findings = row.get("findings") if isinstance(row.get("findings"), list) else []
    messages = [str(item.get("message") or item) for item in findings]
    return {
        "ok": bool(row.get("success")),
        "checks": [str(item.get("check") or "leanparanoia") for item in findings] or ["leanparanoia"],
        "error": "; ".join(messages) if messages else None,
        "source": "leanparanoia",
        "raw_id": row.get("id"),
    }


def safeverify_result(row: dict[str, Any]) -> ToolResult:
    failure = row.get("failure_mode") or row.get("failureMode")
    return {
        "ok": bool(row.get("success")),
        "checks": ["kind", "type", "axioms", "target-submission"],
        "error": None if row.get("success") else str(failure or "SafeVerify failed"),
        "source": "safeverify",
        "raw_id": row.get("id"),
    }


def autograder_problem_result(problem: dict[str, Any], parent: dict[str, Any]) -> ToolResult:
    return {
        "ok": bool(problem.get("passed")),
        "checks": ["autograder-score"],
        "error": None if problem.get("passed") else str(problem.get("message") or problem.get("status") or "autograder failed"),
        "source": "lean4_autograder",
        "raw_id": problem.get("id") or parent.get("id"),
        "score": {"earned": float(problem.get("earned") or 0), "total": float(problem.get("points") or 0)},
    }


def promotion_result(row: dict[str, Any]) -> ToolResult:
    violations = row.get("violations") if isinstance(row.get("violations"), list) else []
    messages = [str(item.get("message") or item) for item in violations]
    return {
        "ok": bool(row.get("promotion_allowed")),
        "checks": [str(item.get("code") or "promotion-gate") for item in violations] or ["promotion-gate"],
        "error": "; ".join(messages) if messages else None,
        "source": "hive_spec_submission_policy",
        "raw_id": row.get("packet_key"),
        "score": row.get("autograder_points") if isinstance(row.get("autograder_points"), dict) else None,
    }


def merge_reports(
    *,
    decl_paths: list[Path],
    leanparanoia_path: Path | None = None,
    safeverify_path: Path | None = None,
    autograder_path: Path | None = None,
    promotion_path: Path | None = None,
) -> dict[str, Any]:
    table = load_declarations(decl_paths)

    for row in load_json_docs(leanparanoia_path):
        decl = decl_of(row)
        if decl:
            add_tool(table, decl, "leanparanoia", leanparanoia_result(row), module=module_of(row), kind=kind_of(row))

    for index, row in enumerate(load_json_docs(safeverify_path)):
        decl = decl_of(row, fallback=f"safeverify:{index}")
        if decl:
            add_tool(table, decl, "safeverify", safeverify_result(row), module=module_of(row), kind=kind_of(row))

    for row in load_json_docs(autograder_path):
        problems = row.get("problems") if isinstance(row.get("problems"), list) else []
        if problems:
            for problem in problems:
                if not isinstance(problem, dict):
                    continue
                decl = decl_of(problem, fallback=str(problem.get("name") or "autograder_problem"))
                if decl:
                    add_tool(table, decl, "autograder", autograder_problem_result(problem, row), kind=str(problem.get("kind") or ""))
        else:
            decl = decl_of(row, fallback=str(row.get("id") or "autograder"))
            add_tool(
                table,
                decl,
                "autograder",
                {
                    "ok": bool(row.get("passed")),
                    "checks": ["autograder-report"],
                    "error": None if row.get("passed") else "autograder report failed",
                    "source": "lean4_autograder",
                    "raw_id": row.get("id"),
                    "score": {"earned": float(row.get("earned_points") or 0), "total": float(row.get("total_points") or 0)},
                },
            )

    for row in load_json_docs(promotion_path):
        decl = decl_of(row, fallback=f"promotion:{row.get('spec_id', 'spec')}::{row.get('submission_id', 'submission')}")
        add_tool(table, decl, "promotion", promotion_result(row))

    declarations = []
    for decl in sorted(table):
        entry = table[decl]
        tools = entry.get("tools") or {}
        ok = bool(tools) and all(bool(result.get("ok")) for result in tools.values())
        errors = [str(result.get("error")) for result in tools.values() if result.get("error")]
        checks = sorted({str(check) for result in tools.values() for check in result.get("checks", [])})
        declarations.append(
            {
                "decl": decl,
                "module": entry.get("module") or "",
                "kind": entry.get("kind") or "",
                "ok": ok,
                "tools": tools,
                "score": entry.get("score") or {"earned": 0.0, "total": 0.0},
                "checks": checks,
                "error": "; ".join(errors) if errors else None,
            }
        )

    tool_names = sorted({tool for row in declarations for tool in row["tools"]})
    by_tool = {}
    for tool in tool_names:
        rows = [row for row in declarations if tool in row["tools"]]
        by_tool[tool] = {
            "records": len(rows),
            "passed": sum(1 for row in rows if row["tools"][tool].get("ok")),
            "failed": sum(1 for row in rows if not row["tools"][tool].get("ok")),
        }

    return {
        "schema": SCHEMA,
        "summary": {
            "total_declarations": len(declarations),
            "with_checker_data": sum(1 for row in declarations if row["tools"]),
            "passed_all": sum(1 for row in declarations if row["ok"]),
            "failed_any": sum(1 for row in declarations if row["tools"] and not row["ok"]),
            "missing_checker_data": sum(1 for row in declarations if not row["tools"]),
            "by_tool": by_tool,
        },
        "declarations": declarations,
        "authority_boundary": {
            "merged_report_is_audit_telemetry": True,
            "not_a_proof_certificate": True,
            "lean_remains_proof_authority": True,
            "promotion_requires_hive_gates": True,
        },
    }


def markdown_report(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# Hive Multi-Checker Report",
        "",
        "This report merges audit/scoring telemetry. It is not a Lean proof certificate.",
        "",
        "## Summary",
        "",
        f"- Total declarations: {summary['total_declarations']}",
        f"- With checker data: {summary['with_checker_data']}",
        f"- Passed all supplied checks: {summary['passed_all']}",
        f"- Failed any supplied check: {summary['failed_any']}",
        f"- Missing checker data: {summary['missing_checker_data']}",
        "",
        "## Tools",
        "",
    ]
    for tool, stats in sorted(summary.get("by_tool", {}).items()):
        lines.append(f"- `{tool}`: {stats['passed']} passed, {stats['failed']} failed, {stats['records']} records")
    lines.extend(["", "## Failures", ""])
    failures = [row for row in report["declarations"] if row["tools"] and not row["ok"]]
    if not failures:
        lines.append("No supplied checker failures.")
    else:
        for row in failures[:200]:
            lines.append(f"- `{row['decl']}`: {row['error'] or 'failed'}")
    lines.append("")
    return "\n".join(lines)


def write_outputs(report: dict[str, Any], json_out: Path, md_out: Path | None) -> None:
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    if md_out:
        md_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.write_text(markdown_report(report), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--decls", type=Path, action="append", default=[], help="Declaration JSON/JSONL artifact used to seed rows")
    parser.add_argument("--leanparanoia-jsonl", type=Path)
    parser.add_argument("--safeverify-jsonl", type=Path)
    parser.add_argument("--autograder-jsonl", type=Path)
    parser.add_argument("--promotion-json", type=Path)
    parser.add_argument("--json-out", type=Path, required=True)
    parser.add_argument("--md-out", type=Path)
    args = parser.parse_args()

    report = merge_reports(
        decl_paths=list(args.decls),
        leanparanoia_path=args.leanparanoia_jsonl,
        safeverify_path=args.safeverify_jsonl,
        autograder_path=args.autograder_jsonl,
        promotion_path=args.promotion_json,
    )
    write_outputs(report, args.json_out, args.md_out)
    print(json.dumps(report["summary"], indent=2, ensure_ascii=True, sort_keys=True))
    return 0 if report["summary"]["failed_any"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
