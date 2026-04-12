#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import statistics
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root


DEFAULT_TARGETS = [
    "lean/InfoGeometry/Canonical/MasterSynthesis.lean",
    "lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean",
    "lean/InfoGeometry/Canonical/BekensteinBound.lean",
]
DEFAULT_JSON_OUT = "reports/dag/hypothesis-debt-index.json"
DEFAULT_MD_OUT = "reports/dag/hypothesis-debt-index.md"

DECL_RE = re.compile(r"^\s*(?:private\s+|protected\s+)?(?P<kind>theorem|lemma)\s+(?P<name>[^\s\(:=]+)")
BRIDGE_TYPE_RE = re.compile(r"\b(Bridge|Compatibility|Assumption|Hypoth|Surface|Witness|Package|Data)\b")
PREDICATE_TYPE_RE = re.compile(r"\b(?:Is|Has|Satisfies|Exists|Nonempty)\w*")


@dataclass
class DeclDebtRow:
    file: str
    line: int
    kind: str
    name: str
    explicit_binders: int
    implicit_binders: int
    instance_binders: int
    hypothesis_name_vars: int
    prop_type_vars: int
    bridge_type_vars: int
    predicate_type_vars: int
    signature_lines: int
    score: float


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Rank theorem surfaces by hypothesis/interface debt for selected Lean files. "
            "The report is source-text based and intended for synthesis-layer packaging audits."
        )
    )
    parser.add_argument(
        "--targets",
        action="append",
        default=[],
        help="Lean file path to analyze (repeatable). Defaults to synthesis files.",
    )
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT, help="JSON output path.")
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT, help="Markdown output path.")
    parser.add_argument("--top", type=int, default=20, help="Top rows to keep in report tables.")
    return parser.parse_args()


def normalize_target_path(root: Path, raw: str) -> Path:
    p = Path(raw)
    if p.is_absolute():
        return p.resolve()
    return (root / p).resolve()


def load_targets(root: Path, raw_targets: list[str]) -> list[Path]:
    targets = raw_targets if raw_targets else list(DEFAULT_TARGETS)
    resolved = [normalize_target_path(root, t) for t in targets]
    missing = [p for p in resolved if not p.exists()]
    if missing:
        missing_rel = ", ".join(str(p) for p in missing)
        raise SystemExit(f"[hypothesis-debt] missing target files: {missing_rel}")
    return resolved


def find_signature_end(lines: list[str], start_idx: int) -> int:
    for idx in range(start_idx, min(len(lines), start_idx + 300)):
        if ":=" in lines[idx]:
            return idx
    return min(len(lines) - 1, start_idx + 40)


def find_top_level_colon(s: str) -> int | None:
    stack: list[str] = []
    pairs = {")": "(", "}": "{", "]": "["}
    for i, ch in enumerate(s):
        if ch in "([{":
            stack.append(ch)
            continue
        if ch in ")]}":
            if stack and stack[-1] == pairs[ch]:
                stack.pop()
            continue
        if ch == ":" and not stack:
            nxt = s[i + 1] if i + 1 < len(s) else ""
            if nxt != "=":
                return i
    return None


def split_names(names_raw: str) -> list[str]:
    cleaned = " ".join(names_raw.replace("\n", " ").split())
    if not cleaned:
        return []
    out: list[str] = []
    for tok in cleaned.split(" "):
        if tok in {"_", ""}:
            continue
        out.append(tok)
    return out


def is_hypothesis_name(name: str) -> bool:
    n = name.lstrip("_")
    return n.startswith("h") or "hyp" in n.lower() or "assum" in n.lower()


def type_is_prop_like(typ: str) -> bool:
    t = typ.strip()
    if "Prop" in t:
        return True
    return any(sym in t for sym in ("=", "≠", "<", ">", "≤", "≥"))


def parse_top_level_binders(binder_zone: str) -> list[tuple[str, str, list[str], str]]:
    binders: list[tuple[str, str, list[str], str]] = []
    i = 0
    n = len(binder_zone)
    pairs = {")": "(", "}": "{", "]": "["}
    while i < n:
        ch = binder_zone[i]
        if ch not in "([{":
            i += 1
            continue
        opener = ch
        stack = [opener]
        j = i + 1
        while j < n and stack:
            cj = binder_zone[j]
            if cj in "([{":
                stack.append(cj)
            elif cj in ")]}":
                if stack and stack[-1] == pairs[cj]:
                    stack.pop()
            j += 1
        if stack:
            break
        body = binder_zone[i + 1 : j - 1]
        if ":" in body:
            names_raw, typ = body.split(":", 1)
            names = split_names(names_raw)
            if not names:
                names = ["_"]
            binders.append((opener, body, names, typ.strip()))
        else:
            # Instance-style binder, e.g. `[CompleteSpace E]`.
            binders.append((opener, body, ["_inst"], body.strip()))
        i = j
    return binders


def extract_decl_row(file_rel: str, line_no: int, kind: str, name: str, signature: str, signature_lines: int) -> DeclDebtRow:
    # Keep binder parsing to the declaration zone before the theorem statement colon.
    m = DECL_RE.match(signature.splitlines()[0])
    after_name = signature
    if m:
        first = signature.splitlines()[0]
        tail0 = first[m.end() :]
        tail_rest = signature.splitlines()[1:]
        after_name = "\n".join([tail0] + tail_rest)
    colon_idx = find_top_level_colon(after_name)
    binder_zone = after_name[:colon_idx] if colon_idx is not None else after_name

    explicit = 0
    implicit = 0
    inst = 0
    hyp_name_vars = 0
    prop_type_vars = 0
    bridge_type_vars = 0
    predicate_type_vars = 0

    for opener, _body, names, typ in parse_top_level_binders(binder_zone):
        count = max(len(names), 1)
        if opener == "(":
            explicit += count
        elif opener == "{":
            implicit += count
        elif opener == "[":
            inst += count

        for nm in names:
            if is_hypothesis_name(nm):
                hyp_name_vars += 1

        if type_is_prop_like(typ):
            prop_type_vars += count
        if BRIDGE_TYPE_RE.search(typ):
            bridge_type_vars += count
        if PREDICATE_TYPE_RE.search(typ):
            predicate_type_vars += count

    score = (
        3.0 * hyp_name_vars
        + 2.0 * prop_type_vars
        + 4.0 * bridge_type_vars
        + 1.0 * predicate_type_vars
        + 0.5 * inst
        + 0.1 * implicit
    )

    return DeclDebtRow(
        file=file_rel,
        line=line_no,
        kind=kind,
        name=name,
        explicit_binders=explicit,
        implicit_binders=implicit,
        instance_binders=inst,
        hypothesis_name_vars=hyp_name_vars,
        prop_type_vars=prop_type_vars,
        bridge_type_vars=bridge_type_vars,
        predicate_type_vars=predicate_type_vars,
        signature_lines=signature_lines,
        score=round(score, 3),
    )


def collect_rows(root: Path, targets: list[Path]) -> list[DeclDebtRow]:
    rows: list[DeclDebtRow] = []
    for path in targets:
        rel = str(path.resolve().relative_to(root))
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
        i = 0
        while i < len(lines):
            m = DECL_RE.match(lines[i])
            if not m:
                i += 1
                continue
            end = find_signature_end(lines, i)
            signature = "\n".join(lines[i : end + 1])
            row = extract_decl_row(
                file_rel=rel,
                line_no=i + 1,
                kind=m.group("kind"),
                name=m.group("name"),
                signature=signature,
                signature_lines=(end - i + 1),
            )
            rows.append(row)
            i = end + 1
    rows.sort(key=lambda r: (-r.score, r.file, r.line, r.name))
    return rows


def summarize(rows: list[DeclDebtRow]) -> dict[str, Any]:
    by_file: dict[str, list[DeclDebtRow]] = {}
    for r in rows:
        by_file.setdefault(r.file, []).append(r)
    file_rows: list[dict[str, Any]] = []
    for file_name in sorted(by_file):
        vals = [r.score for r in by_file[file_name]]
        file_rows.append(
            {
                "file": file_name,
                "decl_count": len(vals),
                "score_total": round(sum(vals), 3),
                "score_mean": round(statistics.fmean(vals) if vals else 0.0, 3),
                "score_max": round(max(vals) if vals else 0.0, 3),
            }
        )
    return {
        "decl_count": len(rows),
        "file_count": len(by_file),
        "files": file_rows,
    }


def render_md(
    generated_at: str,
    targets: list[str],
    summary: dict[str, Any],
    top_rows: list[DeclDebtRow],
) -> str:
    lines: list[str] = []
    lines.append("# Hypothesis Debt Index")
    lines.append("")
    lines.append(f"- generated_at: `{generated_at}`")
    lines.append(f"- declarations_scored: `{summary['decl_count']}`")
    lines.append(f"- files_scored: `{summary['file_count']}`")
    lines.append("")
    lines.append("## Target Files")
    lines.append("")
    for t in targets:
        lines.append(f"- `{t}`")
    lines.append("")
    lines.append("## File Summary")
    lines.append("")
    lines.append("| file | decl_count | score_total | score_mean | score_max |")
    lines.append("| --- | ---: | ---: | ---: | ---: |")
    for row in summary["files"]:
        lines.append(
            f"| `{row['file']}` | {row['decl_count']} | {row['score_total']} | {row['score_mean']} | {row['score_max']} |"
        )
    lines.append("")
    lines.append("## Top Debt Surfaces")
    lines.append("")
    lines.append(
        "| rank | score | declaration | location | h_names | bridge_types | prop_types | predicates | explicit | implicit | instances |"
    )
    lines.append("| ---: | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for idx, row in enumerate(top_rows, start=1):
        lines.append(
            f"| {idx} | {row.score} | `{row.name}` | `{row.file}:{row.line}` | "
            f"{row.hypothesis_name_vars} | {row.bridge_type_vars} | {row.prop_type_vars} | "
            f"{row.predicate_type_vars} | {row.explicit_binders} | {row.implicit_binders} | {row.instance_binders} |"
        )
    lines.append("")
    lines.append(
        "Debt score heuristic: `3*hypothesis_names + 2*prop_types + 4*bridge_types + 1*predicate_types + 0.5*instances + 0.1*implicit`."
    )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    root = repo_root().resolve()
    targets = load_targets(root, list(args.targets))

    rows = collect_rows(root, targets)
    summary = summarize(rows)
    top_rows = rows[: max(args.top, 0)]
    generated_at = datetime.now(timezone.utc).isoformat(timespec="seconds")

    payload = {
        "generated_at": generated_at,
        "targets": [str(p.resolve().relative_to(root)) for p in targets],
        "summary": summary,
        "top": [asdict(r) for r in top_rows],
        "rows": [asdict(r) for r in rows],
    }

    json_out = normalize_target_path(root, args.json_out)
    md_out = normalize_target_path(root, args.md_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)

    json_out.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    md_out.write_text(
        render_md(
            generated_at=generated_at,
            targets=payload["targets"],
            summary=summary,
            top_rows=top_rows,
        ),
        encoding="utf-8",
    )

    print(f"[hypothesis-debt] wrote {json_out.relative_to(root)}")
    print(f"[hypothesis-debt] wrote {md_out.relative_to(root)}")
    print(f"[hypothesis-debt] scored declarations={summary['decl_count']} files={summary['file_count']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
