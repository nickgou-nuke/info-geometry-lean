#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.quality.common import QUARANTINE_MANIFEST_PATH
    from tools.pathing import default_decl_metadata_file, repo_root
else:
    from tools.quality.common import QUARANTINE_MANIFEST_PATH
    from tools.pathing import default_decl_metadata_file, repo_root


DEFAULT_DECLS = str(default_decl_metadata_file().relative_to(repo_root()))
DEFAULT_THINNESS_INDEX = "BRIDGE_THINNESS_INDEX.md"
DEFAULT_VACUITY_INDEX = "VACUITY_INDEX.md"
DEFAULT_SURROGATE_INDEX = "SURROGATE_INDEX.md"
DEFAULT_QUARANTINE_MANIFEST = str(QUARANTINE_MANIFEST_PATH.relative_to(repo_root()))
DEFAULT_MD_OUT = "reports/dag/theorem-surface-index.md"
DEFAULT_JSON_OUT = "reports/dag/theorem-surface-index.json"

QUEUE_HEADERS = {"## Queue", "## Aggressive Replacement Queue"}
QUEUE_RE = re.compile(
    r"^- `(?P<priority>[^`]+)` `(?P<category>[^`]+)` (?P<name>.+?) "
    r"at `(?P<file>[^`:]+)(?::(?P<line>\d+))?`$"
)
HYPOTHESIS_NAME_RE = re.compile(
    r"(?:_of_.*hypotheses\b|_state_hypotheses\b|_components?_state_hypotheses\b|"
    r"_of_.*assumptions?\b|_of_hypothesis\b)",
    re.IGNORECASE,
)
HYPOTHESIS_CONTEXT_PATTERNS = (
    "hypotheses",
    "hypothesis",
    "assumption",
    "assumptions",
    "caller-supplied",
    "caller supplied",
    "if the capstone supplies",
)
PACKAGE_PATTERNS = (
    "package",
    "packages",
    "packaged",
    "repackage",
    "repackages",
    "reproject",
    "reprojects",
    "readback",
    "stored witness",
    "stored witnesses",
    "stores obligations",
    "stores the",
    "facade re-exports",
    "facade reexports",
    "thin descent wrapper",
    "later projects them out",
    "projects stored",
)
SURROGATE_PATTERNS = (
    "surrogate",
    "vacuity",
    "placeholder",
    "identity transport",
    "degenerate",
    "tautological",
    "zero quadratic",
    "scaled-zero",
    "scaled zero",
    "hardcodes identity",
    "collapsed to scalar multiples",
)
ANALYZED_KINDS = {"theorem", "def", "opaque"}
THEOREM_KINDS = {"theorem"}
DEFINITION_KINDS = {"def", "opaque"}


@dataclass
class DeclRow:
    name: str
    short_name: str
    kind: str
    module: str
    file: str
    line: int | None
    category: str
    confidence: str
    signals: list[str]
    audit_hits: list[str]
    quarantine_reason: str | None


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Classify exported InfoGeometry declarations into likely constructive derivations, "
            "hypothesis bridges, package/reprojection surfaces, surrogate/vacuous surfaces, "
            "and neutral definitions."
        )
    )
    ap.add_argument("--decls", default=DEFAULT_DECLS, help="Declaration metadata JSONL path.")
    ap.add_argument("--thinness-index", default=DEFAULT_THINNESS_INDEX)
    ap.add_argument("--vacuity-index", default=DEFAULT_VACUITY_INDEX)
    ap.add_argument("--surrogate-index", default=DEFAULT_SURROGATE_INDEX)
    ap.add_argument("--quarantine-manifest", default=DEFAULT_QUARANTINE_MANIFEST)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--top", type=int, default=20, help="Rows to show per category in markdown.")
    return ap.parse_args()


def normalize_user_path(path: str, root: Path) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate.resolve()
    return (root / candidate).resolve()


def normalize_repo_relative(root: Path, raw: Any) -> str:
    value = str(raw or "").strip()
    if not value or value == "unknown":
        return value
    candidate = Path(value)
    if candidate.is_absolute():
        try:
            return str(candidate.resolve().relative_to(root))
        except ValueError:
            return value
    if str(candidate).startswith("lean/"):
        return str(candidate)
    lean_candidate = root / "lean" / candidate
    if lean_candidate.exists():
        return str(Path("lean") / candidate)
    return str(candidate)


def load_decl_rows(path: Path, root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        obj = json.loads(line)
        kind = str(obj.get("kind", "")).strip()
        if kind not in ANALYZED_KINDS:
            continue
        file_name = normalize_repo_relative(root, obj.get("file", ""))
        if not file_name.startswith("lean/InfoGeometry/"):
            continue
        name = str(obj.get("name", "")).strip()
        if not name:
            continue
        rows.append(
            {
                "name": name,
                "short_name": name.split(".")[-1],
                "kind": kind,
                "module": str(obj.get("module", "")).strip(),
                "file": file_name,
                "line": obj.get("line"),
                "doc": str(obj.get("doc", "") or "").strip(),
            }
        )
    rows.sort(key=lambda row: (row["file"], int(row["line"] or 0), row["name"]))
    return rows


def load_queue(path: Path, index_name: str, root: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    findings: list[dict[str, Any]] = []
    active_queue = False
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        stripped = raw_line.strip()
        if stripped.startswith("## "):
            active_queue = stripped in QUEUE_HEADERS
            continue
        if not active_queue:
            continue
        match = QUEUE_RE.match(stripped)
        if not match:
            continue
        findings.append(
            {
                "index": index_name,
                "priority": match.group("priority"),
                "category": match.group("category"),
                "name": match.group("name"),
                "file": normalize_repo_relative(root, match.group("file")),
                "line": int(match.group("line")) if match.group("line") else None,
            }
        )
    return findings


def load_quarantine_manifest(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    out: dict[str, str] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "|" not in line:
            continue
        module, reason = [chunk.strip() for chunk in line.split("|", 1)]
        if module:
            out[module] = reason
    return out


def context_window(file_cache: dict[str, list[str]], root: Path, file_name: str, line: int | None, radius: int = 6) -> str:
    if line is None:
        return ""
    lines = file_cache.get(file_name)
    if lines is None:
        path = root / file_name
        try:
            lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
        except OSError:
            lines = []
        file_cache[file_name] = lines
    if not lines:
        return ""
    start = max(0, line - 1 - radius)
    end = min(len(lines), line - 1 + radius)
    return "\n".join(lines[start:end]).lower()


def strongest_quarantine_bucket(reason: str | None) -> tuple[str | None, list[str]]:
    if not reason:
        return None, []
    lowered = reason.lower()
    if any(token in lowered for token in SURROGATE_PATTERNS):
        return "surrogate_or_vacuous", [f"quarantine_reason:{reason}"]
    if any(token in lowered for token in PACKAGE_PATTERNS) or "depends on quarantined" in lowered or "re-exports quarantined" in lowered:
        return "package_reprojection", [f"quarantine_reason:{reason}"]
    return None, []


def match_audits(decl: dict[str, Any], findings: list[dict[str, Any]]) -> list[str]:
    hits: list[str] = []
    decl_name = str(decl["name"])
    short_name = str(decl["short_name"])
    file_name = str(decl["file"])
    line = decl.get("line")
    for finding in findings:
        if finding.get("file") != file_name:
            continue
        name = str(finding.get("name", "")).strip()
        line_match = line is not None and finding.get("line") is not None and abs(int(line) - int(finding["line"])) <= 3
        name_match = bool(name) and (decl_name.endswith(name) or short_name == name or name in decl_name)
        if line_match or name_match:
            hits.append(f"{finding['index']}:{finding['category']}:{finding['priority']}")
    return sorted(set(hits))


def classify_decl(
    decl: dict[str, Any],
    *,
    context: str,
    quarantine_reason: str | None,
    audit_hits: list[str],
) -> DeclRow:
    signals: list[str] = []
    lowered_name = decl["name"].lower()
    lowered_doc = decl.get("doc", "").lower()
    combined_context = "\n".join(part for part in [lowered_doc, context] if part)

    quarantine_bucket, quarantine_signals = strongest_quarantine_bucket(quarantine_reason)
    signals.extend(quarantine_signals)

    name_hypothesis = bool(HYPOTHESIS_NAME_RE.search(lowered_name))
    hypothesis_signal = name_hypothesis or any(token in combined_context for token in HYPOTHESIS_CONTEXT_PATTERNS)
    package_signal = any(token in combined_context for token in PACKAGE_PATTERNS)
    surrogate_signal = any(token in combined_context for token in SURROGATE_PATTERNS)

    if name_hypothesis:
        signals.append("name:hypotheses")
    if any(token in combined_context for token in HYPOTHESIS_CONTEXT_PATTERNS):
        signals.append("context:hypotheses")
    if package_signal:
        signals.append("context:packaging")
    if surrogate_signal:
        signals.append("context:surrogate")
    if audit_hits:
        signals.extend(f"audit:{hit}" for hit in audit_hits)

    if audit_hits or surrogate_signal or quarantine_bucket == "surrogate_or_vacuous":
        category = "surrogate_or_vacuous"
        confidence = "high" if audit_hits or quarantine_bucket == "surrogate_or_vacuous" else "medium"
    elif decl["kind"] in THEOREM_KINDS and hypothesis_signal:
        category = "hypothesis_bridge"
        confidence = "high" if name_hypothesis else "medium"
    elif quarantine_bucket == "package_reprojection" or package_signal:
        category = "package_reprojection"
        confidence = "high" if quarantine_bucket == "package_reprojection" else "medium"
    elif decl["kind"] in DEFINITION_KINDS:
        category = "neutral_definition"
        confidence = "low"
    else:
        category = "likely_constructive"
        confidence = "low"

    return DeclRow(
        name=decl["name"],
        short_name=decl["short_name"],
        kind=decl["kind"],
        module=decl["module"],
        file=decl["file"],
        line=int(decl["line"]) if decl.get("line") is not None else None,
        category=category,
        confidence=confidence,
        signals=sorted(dict.fromkeys(signals)),
        audit_hits=audit_hits,
        quarantine_reason=quarantine_reason,
    )


def render_md(payload: dict[str, Any], top: int) -> str:
    summary = payload["summary"]
    lines: list[str] = []
    lines.append("# Theorem Surface Index")
    lines.append("")
    lines.append("This report is a heuristic declaration-level classification, not kernel truth.")
    lines.append("It distinguishes likely constructive declarations from hypothesis bridges, package/reprojection surfaces, and surrogate/vacuous surfaces using the exported declaration inventory, tracked debt indices, quarantine annotations, and local source context.")
    lines.append("")
    lines.append("## Summary")
    lines.append(f"- analyzed declarations: `{summary['analyzed_declarations']}`")
    lines.append(f"- theorem declarations: `{summary['theorem_declarations']}`")
    lines.append(f"- definition declarations: `{summary['definition_declarations']}`")
    lines.append(f"- likely constructive: `{summary['category_counts']['likely_constructive']}`")
    lines.append(f"- hypothesis bridges: `{summary['category_counts']['hypothesis_bridge']}`")
    lines.append(f"- package / reprojection surfaces: `{summary['category_counts']['package_reprojection']}`")
    lines.append(f"- surrogate / vacuous surfaces: `{summary['category_counts']['surrogate_or_vacuous']}`")
    lines.append(f"- neutral definitions: `{summary['category_counts']['neutral_definition']}`")
    lines.append(f"- declarations with audit hits: `{summary['audit_hit_declarations']}`")
    lines.append(f"- declarations in quarantined modules: `{summary['quarantined_module_declarations']}`")
    lines.append("")
    lines.append("## Category Notes")
    lines.append("- `likely_constructive`: theorem declarations with no current bridge/package/surrogate warning signal.")
    lines.append("- `hypothesis_bridge`: theorem names or local comments explicitly advertise hypothesis-driven transport such as `_of_*_hypotheses`.")
    lines.append("- `package_reprojection`: declarations whose module reason or local comments say they package, store, read back, or reproject witnesses/obligations.")
    lines.append("- `surrogate_or_vacuous`: declarations hit by the live debt audits or living on surfaces marked vacuous/degenerate/identity-transport in the quarantine manifest.")
    lines.append("- `neutral_definition`: definitions and opaque wrappers without a stronger warning signal.")
    lines.append("")

    sections = [
        ("surrogate_or_vacuous", "Surrogate / Vacuous Surfaces"),
        ("package_reprojection", "Package / Reprojection Surfaces"),
        ("hypothesis_bridge", "Hypothesis Bridges"),
        ("likely_constructive", "Likely Constructive Declarations"),
    ]
    for category, title in sections:
        rows = payload["top_examples"][category]
        lines.append(f"## {title}")
        if not rows:
            lines.append("- none")
        else:
            for row in rows[:top]:
                location = f"{row['file']}:{row['line']}" if row.get("line") else row["file"]
                signal_text = "; ".join(row.get("signals", [])[:3]) if row.get("signals") else "-"
                lines.append(
                    f"- `{row['name']}` | `{row['kind']}` | `{location}` | confidence `{row['confidence']}` | signals: {signal_text}"
                )
        lines.append("")

    lines.append("## Modules With Highest Non-Constructive Load")
    if payload["module_rollup"]:
        lines.append("| Module | Hypothesis bridges | Package surfaces | Surrogate/vacuous | Total |")
        lines.append("| :--- | ---: | ---: | ---: | ---: |")
        for row in payload["module_rollup"][:top]:
            lines.append(
                f"| `{row['module']}` | {row['hypothesis_bridge']} | {row['package_reprojection']} | {row['surrogate_or_vacuous']} | {row['total']} |"
            )
    else:
        lines.append("- none")
    lines.append("")

    lines.append("## Quarantine Anchors")
    if payload["quarantined_modules"]:
        for row in payload["quarantined_modules"][:top]:
            lines.append(f"- `{row['module']}` | {row['reason']}")
    else:
        lines.append("- none")
    lines.append("")

    lines.append("## Interpretation")
    lines.append("- This index is intentionally conservative: a declaration is only marked suspicious when the live audits, the quarantine manifest, the declaration name, or the local source context say so.")
    lines.append("- A declaration in `likely_constructive` is not proved to be deep; it simply lacks the current signals of packaging or vacuity.")
    lines.append("- Use this report together with the quarantine manifest and debt indices to decide what deserves promotion or demolition.")
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    root = repo_root()
    decls_path = normalize_user_path(args.decls, root)
    thinness_path = normalize_user_path(args.thinness_index, root)
    vacuity_path = normalize_user_path(args.vacuity_index, root)
    surrogate_path = normalize_user_path(args.surrogate_index, root)
    quarantine_manifest_path = normalize_user_path(args.quarantine_manifest, root)
    md_out = normalize_user_path(args.md_out, root)
    json_out = normalize_user_path(args.json_out, root)

    decls = load_decl_rows(decls_path, root)
    findings = (
        load_queue(thinness_path, "thinness", root)
        + load_queue(vacuity_path, "vacuity", root)
        + load_queue(surrogate_path, "surrogate", root)
    )
    quarantine = load_quarantine_manifest(quarantine_manifest_path)
    file_cache: dict[str, list[str]] = {}

    rows: list[DeclRow] = []
    for decl in decls:
        context = context_window(file_cache, root, decl["file"], decl.get("line"))
        quarantine_reason = quarantine.get(decl["module"])
        audit_hits = match_audits(decl, findings)
        rows.append(
            classify_decl(
                decl,
                context=context,
                quarantine_reason=quarantine_reason,
                audit_hits=audit_hits,
            )
        )

    category_counts = Counter(row.category for row in rows)
    module_rollup_map: dict[str, Counter[str]] = defaultdict(Counter)
    for row in rows:
        if row.category in {"hypothesis_bridge", "package_reprojection", "surrogate_or_vacuous"}:
            module_rollup_map[row.module][row.category] += 1
            module_rollup_map[row.module]["total"] += 1

    module_rollup = sorted(
        (
            {
                "module": module,
                "hypothesis_bridge": counts.get("hypothesis_bridge", 0),
                "package_reprojection": counts.get("package_reprojection", 0),
                "surrogate_or_vacuous": counts.get("surrogate_or_vacuous", 0),
                "total": counts.get("total", 0),
            }
            for module, counts in module_rollup_map.items()
        ),
        key=lambda row: (-row["total"], -row["surrogate_or_vacuous"], row["module"]),
    )

    def rank_key(row: DeclRow) -> tuple[int, int, str, int, str]:
        confidence_rank = {"high": 2, "medium": 1, "low": 0}[row.confidence]
        theorem_rank = 1 if row.kind in THEOREM_KINDS else 0
        return (-confidence_rank, -theorem_rank, row.file, int(row.line or 0), row.name)

    top_examples = {
        category: [asdict(row) for row in sorted((r for r in rows if r.category == category), key=rank_key)]
        for category in [
            "surrogate_or_vacuous",
            "package_reprojection",
            "hypothesis_bridge",
            "likely_constructive",
            "neutral_definition",
        ]
    }

    payload = {
        "source": str(decls_path.relative_to(root)),
        "summary": {
            "analyzed_declarations": len(rows),
            "theorem_declarations": sum(1 for row in rows if row.kind in THEOREM_KINDS),
            "definition_declarations": sum(1 for row in rows if row.kind in DEFINITION_KINDS),
            "category_counts": {
                "likely_constructive": category_counts.get("likely_constructive", 0),
                "hypothesis_bridge": category_counts.get("hypothesis_bridge", 0),
                "package_reprojection": category_counts.get("package_reprojection", 0),
                "surrogate_or_vacuous": category_counts.get("surrogate_or_vacuous", 0),
                "neutral_definition": category_counts.get("neutral_definition", 0),
            },
            "audit_hit_declarations": sum(1 for row in rows if row.audit_hits),
            "quarantined_module_declarations": sum(1 for row in rows if row.quarantine_reason),
        },
        "quarantined_modules": [
            {"module": module, "reason": reason}
            for module, reason in sorted(quarantine.items())
        ],
        "module_rollup": module_rollup,
        "top_examples": top_examples,
        "rows": [asdict(row) for row in rows],
    }

    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(render_md(payload, args.top), encoding="utf-8")
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[theorem-surface-index] wrote {md_out}")
    print(f"[theorem-surface-index] wrote {json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
