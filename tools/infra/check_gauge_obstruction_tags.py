#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import default_src_root, normalize_user_path, repo_root
else:
    from tools.pathing import default_src_root, normalize_user_path, repo_root


DEFAULT_SRC_ROOT = str(default_src_root().relative_to(repo_root()))
DEFAULT_JSON_OUT = "reports/dag/gauge-obstruction-tags.json"
DEFAULT_MD_OUT = "reports/dag/gauge-obstruction-tags.md"
REPORT_SCHEMA_VERSION = 1


DECL_START_RE = re.compile(
    r"^\s*(?:(?:private|protected)\s+)*(?P<kind>theorem|lemma)\s+(?P<name>[^\s(:]+)"
)
NONZERO_RE = re.compile(r"(\bgaugeObstruction\b.*?≠\s*0)|(0\s*≠.*?\bgaugeObstruction\b)", re.DOTALL)
ZERO_RE = re.compile(r"(\bgaugeObstruction\b.*?=\s*0)|(0\s*=.*?\bgaugeObstruction\b)", re.DOTALL)


@dataclass
class DeclarationHit:
    kind: str
    name: str
    line: int
    classification: str
    signature: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Scan Lean theorem/lemma surfaces for gauge-obstruction nonzero statements and emit "
            "anomaly-bearing file tags."
        )
    )
    parser.add_argument("--src-root", default=DEFAULT_SRC_ROOT, help="Lean source root to scan.")
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT, help="JSON report output path.")
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT, help="Markdown report output path.")
    parser.add_argument("--top", type=int, default=25, help="Top-N files in markdown summary tables.")
    parser.add_argument(
        "--fail-on-any-anomaly-bearing",
        action="store_true",
        help="Fail with exit code 2 when any file is tagged anomaly-bearing.",
    )
    parser.add_argument(
        "--fail-on-anomaly-bearing-path",
        action="append",
        default=[],
        help=(
            "Fail with exit code 2 when an anomaly-bearing file is under this relative path prefix. "
            "May be repeated."
        ),
    )
    return parser.parse_args()


def normalize_signature(text: str) -> str:
    collapsed = " ".join(text.split())
    return collapsed[:400] + (" ..." if len(collapsed) > 400 else "")


def split_signature_and_conclusion(decl_text: str) -> tuple[str, str]:
    signature = decl_text.split(":=", 1)[0]
    if ":" in signature:
        proposition = signature.rsplit(":", 1)[1]
    else:
        proposition = signature
    conclusion = re.split(r"→|->", proposition)[-1]
    return proposition, conclusion


def classify_declaration(decl_text: str) -> str | None:
    if "gaugeObstruction" not in decl_text:
        return None
    proposition, conclusion = split_signature_and_conclusion(decl_text)
    prop_has_nonzero = NONZERO_RE.search(proposition) is not None
    conc_has_nonzero = NONZERO_RE.search(conclusion) is not None
    conc_has_zero = ZERO_RE.search(conclusion) is not None
    if conc_has_nonzero:
        return "proves_nonzero"
    if prop_has_nonzero:
        return "assumes_nonzero"
    if conc_has_zero:
        return "proves_zero"
    return "mentions_only"


def extract_hits(path: Path) -> list[DeclarationHit]:
    text = path.read_text(encoding="utf-8")
    if "gaugeObstruction" not in text:
        return []

    hits: list[DeclarationHit] = []
    lines = text.splitlines()
    current_lines: list[str] = []
    current_name = ""
    current_kind = ""
    current_line = 0

    def flush_current() -> None:
        nonlocal current_lines, current_name, current_kind, current_line
        if not current_lines:
            return
        decl_text = "\n".join(current_lines)
        classification = classify_declaration(decl_text)
        if classification is not None:
            hits.append(
                DeclarationHit(
                    kind=current_kind,
                    name=current_name,
                    line=current_line,
                    classification=classification,
                    signature=normalize_signature(decl_text.split(":=", 1)[0]),
                )
            )
        current_lines = []
        current_name = ""
        current_kind = ""
        current_line = 0

    for idx, line in enumerate(lines, start=1):
        start = DECL_START_RE.match(line)
        if start:
            if current_lines:
                flush_current()
            current_lines = [line]
            current_name = start.group("name")
            current_kind = start.group("kind")
            current_line = idx
            if ":=" in line:
                flush_current()
            continue

        if current_lines:
            current_lines.append(line)
            if ":=" in line:
                flush_current()

    flush_current()
    return hits


def file_tag(hits: list[DeclarationHit]) -> str:
    if any(h.classification == "proves_nonzero" for h in hits):
        return "anomaly-bearing"
    if any(h.classification == "assumes_nonzero" for h in hits):
        return "anomaly-sensitive"
    return "gauge-obstruction-lane"


def to_json(
    root: Path, source_root: Path, per_file: dict[Path, list[DeclarationHit]]
) -> dict[str, Any]:
    files_payload: list[dict[str, Any]] = []
    total_decls = 0
    total_proves_nonzero = 0
    total_assumes_nonzero = 0
    total_proves_zero = 0
    total_mentions_only = 0

    for path in sorted(per_file.keys()):
        hits = per_file[path]
        total_decls += len(hits)
        counts = {
            "proves_nonzero": sum(1 for h in hits if h.classification == "proves_nonzero"),
            "assumes_nonzero": sum(1 for h in hits if h.classification == "assumes_nonzero"),
            "proves_zero": sum(1 for h in hits if h.classification == "proves_zero"),
            "mentions_only": sum(1 for h in hits if h.classification == "mentions_only"),
        }
        total_proves_nonzero += counts["proves_nonzero"]
        total_assumes_nonzero += counts["assumes_nonzero"]
        total_proves_zero += counts["proves_zero"]
        total_mentions_only += counts["mentions_only"]
        files_payload.append(
            {
                "path": str(path.relative_to(root)),
                "tag": file_tag(hits),
                "counts": counts,
                "declarations": [
                    {
                        "kind": h.kind,
                        "name": h.name,
                        "line": h.line,
                        "classification": h.classification,
                        "signature": h.signature,
                    }
                    for h in hits
                ],
            }
        )

    anomaly_bearing_files = sum(1 for _p, hs in per_file.items() if any(h.classification == "proves_nonzero" for h in hs))
    anomaly_sensitive_files = sum(1 for _p, hs in per_file.items() if (not any(h.classification == "proves_nonzero" for h in hs)) and any(h.classification == "assumes_nonzero" for h in hs))

    return {
        "schemaVersion": REPORT_SCHEMA_VERSION,
        "sourceRoot": str(source_root.relative_to(root)),
        "summary": {
            "filesScanned": sum(1 for _ in source_root.rglob("*.lean")),
            "filesWithGaugeObstruction": len(per_file),
            "anomalyBearingFiles": anomaly_bearing_files,
            "anomalySensitiveFiles": anomaly_sensitive_files,
            "declarationsTagged": total_decls,
            "declarationsProveNonzero": total_proves_nonzero,
            "declarationsAssumeNonzero": total_assumes_nonzero,
            "declarationsProveZero": total_proves_zero,
            "declarationsMentionOnly": total_mentions_only,
        },
        "files": files_payload,
    }


def write_markdown(payload: dict[str, Any], md_path: Path, top: int) -> None:
    summary = payload["summary"]
    files = payload["files"]
    sorted_files = sorted(
        files,
        key=lambda row: (
            -int(row["counts"]["proves_nonzero"]),
            -int(row["counts"]["assumes_nonzero"]),
            row["path"],
        ),
    )

    lines: list[str] = []
    lines.append("# Gauge Obstruction Tags")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Source root: `{payload['sourceRoot']}`")
    lines.append(f"- Files scanned: `{summary['filesScanned']}`")
    lines.append(f"- Files with `gaugeObstruction`: `{summary['filesWithGaugeObstruction']}`")
    lines.append(f"- `anomaly-bearing` files: `{summary['anomalyBearingFiles']}`")
    lines.append(f"- `anomaly-sensitive` files: `{summary['anomalySensitiveFiles']}`")
    lines.append(f"- Tagged declarations: `{summary['declarationsTagged']}`")
    lines.append(
        f"- Declaration classes: `proves_nonzero={summary['declarationsProveNonzero']}`, "
        f"`assumes_nonzero={summary['declarationsAssumeNonzero']}`, "
        f"`proves_zero={summary['declarationsProveZero']}`, "
        f"`mentions_only={summary['declarationsMentionOnly']}`"
    )
    lines.append("")
    lines.append(f"## Top Files (N={top})")
    lines.append("")
    lines.append("| File | Tag | proves_nonzero | assumes_nonzero | proves_zero | mentions_only |")
    lines.append("|---|---:|---:|---:|---:|---:|")
    for row in sorted_files[:top]:
        counts = row["counts"]
        lines.append(
            f"| `{row['path']}` | `{row['tag']}` | {counts['proves_nonzero']} | "
            f"{counts['assumes_nonzero']} | {counts['proves_zero']} | {counts['mentions_only']} |"
        )
    lines.append("")
    lines.append("## Anomaly-Bearing Declarations")
    lines.append("")
    anomaly_rows = [
        (row["path"], decl)
        for row in sorted_files
        for decl in row["declarations"]
        if decl["classification"] == "proves_nonzero"
    ]
    if not anomaly_rows:
        lines.append("_No declarations tagged as `proves_nonzero`._")
    else:
        for path, decl in anomaly_rows:
            lines.append(
                f"- `{path}:{decl['line']}` `{decl['kind']} {decl['name']}`  "
                f"`[{decl['classification']}]`"
            )
    lines.append("")
    lines.append("## Policy Check")
    lines.append("")
    policy = payload.get("policyCheck", {})
    violation_count = int(policy.get("violationCount", 0))
    if violation_count == 0:
        lines.append("- Status: `PASS`")
    else:
        lines.append(f"- Status: `FAIL` (`violationCount={violation_count}`)")
        for row in policy.get("violations", []):
            lines.append(f"- `{row.get('path', '')}` matched policy `{row.get('policy', '')}`")

    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _normalize_prefix(prefix: str) -> str:
    return prefix.strip().replace("\\", "/").lstrip("./").rstrip("/")


def _matches_prefix(path: str, prefix: str) -> bool:
    if not prefix:
        return False
    return path == prefix or path.startswith(prefix + "/")


def run_policy_check(payload: dict[str, Any], args: argparse.Namespace) -> tuple[list[dict[str, str]], dict[str, Any]]:
    files = payload.get("files", [])
    prefixes = [_normalize_prefix(p) for p in args.fail_on_anomaly_bearing_path]
    prefixes = [p for p in prefixes if p]

    violations: list[dict[str, str]] = []
    for row in files:
        tag = str(row.get("tag", ""))
        if tag != "anomaly-bearing":
            continue
        path = str(row.get("path", ""))
        if args.fail_on_any_anomaly_bearing:
            violations.append({"path": path, "policy": "any-anomaly-bearing"})
            continue
        for prefix in prefixes:
            if _matches_prefix(path, prefix):
                violations.append({"path": path, "policy": f"path-prefix:{prefix}"})
                break

    policy_payload = {
        "failOnAnyAnomalyBearing": bool(args.fail_on_any_anomaly_bearing),
        "failOnAnomalyBearingPaths": prefixes,
        "violationCount": len(violations),
        "violations": violations,
    }
    return violations, policy_payload


def main() -> int:
    args = parse_args()
    root = repo_root()
    source_root = normalize_user_path(args.src_root, root / DEFAULT_SRC_ROOT)
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)

    if not source_root.exists():
        raise SystemExit(f"source root does not exist: {source_root}")

    per_file: dict[Path, list[DeclarationHit]] = {}
    for path in sorted(source_root.rglob("*.lean")):
        hits = extract_hits(path)
        if hits:
            per_file[path] = hits

    payload = to_json(root, source_root, per_file)
    violations, policy_payload = run_policy_check(payload, args)
    payload["policyCheck"] = policy_payload

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    write_markdown(payload, md_out, max(1, int(args.top)))

    summary = payload["summary"]
    print(
        "[gauge-obstruction-tags] "
        f"files_scanned={summary['filesScanned']} "
        f"files_with_gaugeObstruction={summary['filesWithGaugeObstruction']} "
        f"anomaly_bearing={summary['anomalyBearingFiles']} "
        f"declarations_prove_nonzero={summary['declarationsProveNonzero']}",
        flush=True,
    )
    print(f"[gauge-obstruction-tags] wrote {json_out}", flush=True)
    print(f"[gauge-obstruction-tags] wrote {md_out}", flush=True)
    if violations:
        print(
            "[gauge-obstruction-tags] POLICY FAIL "
            f"violation_count={len(violations)}",
            file=sys.stderr,
            flush=True,
        )
        for row in violations:
            print(
                f"[gauge-obstruction-tags] violation path={row['path']} policy={row['policy']}",
                file=sys.stderr,
                flush=True,
            )
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
