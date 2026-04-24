#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import re
import statistics
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.decl_graph_support import GraphProfile, load_decl_graph
    from tools.pathing import repo_root
else:
    from tools.infra.decl_graph_support import GraphProfile, load_decl_graph
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
    visibility: str = "public"
    decl_full_name: str | None = None
    reverse_theorem_users: int = 0
    reverse_value_users: int = 0
    reverse_type_users: int = 0
    graph_support: float = 0.0
    graph_load_bearing_score: float = 0.0
    hybrid_score: float = 0.0
    structural_role: str = "graph_unknown"
    rep_layer: str | None = None
    rep_depth: int | None = None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Rank theorem surfaces by hypothesis/interface debt for selected Lean files. "
            "Lean DAG graph evidence is the authority for structural weight; source-text "
            "binder cues remain only weak hints."
        )
    )
    parser.add_argument("--targets", action="append", default=[], help="Lean file path to analyze (repeatable).")
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT, help="JSON output path.")
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT, help="Markdown output path.")
    parser.add_argument("--top", type=int, default=20, help="Top rows to keep in report tables.")
    parser.add_argument("--include-nonexported", action="store_true", help="Include private/protected theorem surfaces.")
    parser.add_argument("--allow-heuristic-only", action="store_true", help="Allow report generation when graph anchoring is missing.")
    return parser.parse_args()


def normalize_target_path(root: Path, raw: str) -> Path:
    path = Path(raw)
    return path.resolve() if path.is_absolute() else (root / path).resolve()


def load_targets(root: Path, raw_targets: list[str]) -> list[Path]:
    targets = raw_targets if raw_targets else list(DEFAULT_TARGETS)
    resolved = [normalize_target_path(root, target) for target in targets]
    missing = [path for path in resolved if not path.exists()]
    if missing:
        raise SystemExit(f"[hypothesis-debt] missing target files: {', '.join(str(path) for path in missing)}")
    return resolved


def find_signature_end(lines: list[str], start_idx: int) -> int:
    for idx in range(start_idx, min(len(lines), start_idx + 300)):
        if ":=" in lines[idx]:
            return idx
    return min(len(lines) - 1, start_idx + 40)


def find_top_level_colon(text: str) -> int | None:
    stack: list[str] = []
    pairs = {")": "(", "}": "{", "]": "["}
    for i, ch in enumerate(text):
        if ch in "([{":
            stack.append(ch)
            continue
        if ch in ")]}":
            if stack and stack[-1] == pairs[ch]:
                stack.pop()
            continue
        if ch == ":" and not stack:
            nxt = text[i + 1] if i + 1 < len(text) else ""
            if nxt != "=":
                return i
    return None


def split_names(names_raw: str) -> list[str]:
    cleaned = " ".join(names_raw.replace("\n", " ").split())
    return [tok for tok in cleaned.split(" ") if tok not in {"", "_"}]


def is_hypothesis_name(name: str) -> bool:
    n = name.lstrip("_")
    return n.startswith("h") or "hyp" in n.lower() or "assum" in n.lower()


def type_is_prop_like(typ: str) -> bool:
    typ = typ.strip()
    return "Prop" in typ or any(sym in typ for sym in ("=", "≠", "<", ">", "≤", "≥"))


def parse_top_level_binders(binder_zone: str) -> list[tuple[str, list[str], str]]:
    binders: list[tuple[str, list[str], str]] = []
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
            binders.append((opener, split_names(names_raw) or ["_"], typ.strip()))
        else:
            binders.append((opener, ["_inst"], body.strip()))
        i = j
    return binders


def extract_decl_row(file_rel: str, line_no: int, kind: str, name: str, signature: str, signature_lines: int, visibility: str) -> DeclDebtRow:
    match = DECL_RE.match(signature.splitlines()[0])
    after_name = signature
    if match:
        first = signature.splitlines()[0]
        tail0 = first[match.end() :]
        tail_rest = signature.splitlines()[1:]
        after_name = "\n".join([tail0] + tail_rest)
    colon_idx = find_top_level_colon(after_name)
    binder_zone = after_name[:colon_idx] if colon_idx is not None else after_name

    explicit = implicit = inst = 0
    hyp_name_vars = prop_type_vars = bridge_type_vars = predicate_type_vars = 0
    for opener, names, typ in parse_top_level_binders(binder_zone):
        count = max(len(names), 1)
        if opener == "(":
            explicit += count
        elif opener == "{":
            implicit += count
        elif opener == "[":
            inst += count
        hyp_name_vars += sum(1 for nm in names if is_hypothesis_name(nm))
        if type_is_prop_like(typ):
            prop_type_vars += count
        if BRIDGE_TYPE_RE.search(typ):
            bridge_type_vars += count
        if PREDICATE_TYPE_RE.search(typ):
            predicate_type_vars += count

    score = round(3.0 * hyp_name_vars + 2.0 * prop_type_vars + 4.0 * bridge_type_vars + 1.0 * predicate_type_vars + 0.5 * inst + 0.1 * implicit, 3)
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
        score=score,
        visibility=visibility,
    )


def compute_hybrid_priority(row: DeclDebtRow, profile: GraphProfile | None) -> float:
    if profile is None:
        return row.score
    fragility_boost = {
        "isolated_theorem": 2.2,
        "type_only_theorem": 1.8,
        "thin_forwarder": 1.35,
        "supported_theorem": 1.0,
        "load_bearing": 0.7,
        "capstone_endpoint": 0.75,
    }.get(profile.structural_role, 1.0)
    damping = 1.0 + math.log1p(max(profile.graph_load_bearing_score, 0.0))
    return round((row.score * fragility_boost) / damping, 3)


def resolve_decl_full_name(row: DeclDebtRow, decl_key_to_full: dict[tuple[str, int, str], str], graph_profiles: dict[str, GraphProfile], *, max_line_delta: int = 8) -> str | None:
    exact = decl_key_to_full.get((row.file, row.line, row.name))
    if exact is not None:
        return exact
    suffix = f'.{row.name}'
    candidates: list[tuple[int, str]] = []
    for full_name, profile in graph_profiles.items():
        if profile.file != row.file or profile.line is None:
            continue
        if not (full_name == row.name or full_name.endswith(suffix)):
            continue
        delta = abs(profile.line - row.line)
        if delta <= max_line_delta:
            candidates.append((delta, full_name))
    if not candidates:
        return None
    candidates.sort(key=lambda item: (item[0], item[1]))
    return candidates[0][1]


def enrich_rows_with_graph(rows: list[DeclDebtRow], decl_key_to_full: dict[tuple[str, int, str], str], graph_profiles: dict[str, GraphProfile]) -> int:
    anchored = 0
    for row in rows:
        full_name = resolve_decl_full_name(row, decl_key_to_full, graph_profiles)
        row.decl_full_name = full_name
        if full_name is None:
            row.hybrid_score = row.score
            continue
        profile = graph_profiles.get(full_name)
        if profile is None:
            row.hybrid_score = row.score
            continue
        anchored += 1
        row.reverse_theorem_users = profile.reverse_theorem_users
        row.reverse_value_users = profile.reverse_value_users
        row.reverse_type_users = profile.reverse_type_users
        row.graph_support = profile.graph_load_bearing_score
        row.graph_load_bearing_score = profile.graph_load_bearing_score
        row.structural_role = profile.structural_role
        row.rep_layer = profile.rep_layer
        row.rep_depth = profile.rep_depth
        row.hybrid_score = compute_hybrid_priority(row, profile)
    return anchored


def collect_rows(root: Path, targets: list[Path], *, include_nonexported: bool = False) -> list[DeclDebtRow]:
    rows: list[DeclDebtRow] = []
    for path in targets:
        rel = str(path.resolve().relative_to(root))
        lines = path.read_text(encoding='utf-8', errors='ignore').splitlines()
        i = 0
        while i < len(lines):
            match = DECL_RE.match(lines[i])
            if not match:
                i += 1
                continue
            end = find_signature_end(lines, i)
            stripped = lines[i].lstrip()
            visibility = 'private' if stripped.startswith('private theorem') or stripped.startswith('private lemma') else ('protected' if stripped.startswith('protected theorem') or stripped.startswith('protected lemma') else 'public')
            if visibility != 'public' and not include_nonexported:
                i = end + 1
                continue
            signature = '\n'.join(lines[i:end+1])
            rows.append(extract_decl_row(rel, i + 1, match.group('kind'), match.group('name'), signature, end - i + 1, visibility))
            i = end + 1
    return rows


def summarize(rows: list[DeclDebtRow]) -> dict[str, Any]:
    by_file: dict[str, list[DeclDebtRow]] = {}
    for row in rows:
        by_file.setdefault(row.file, []).append(row)
    file_rows: list[dict[str, Any]] = []
    for file_name in sorted(by_file):
        lexical_vals = [row.score for row in by_file[file_name]]
        hybrid_vals = [row.hybrid_score for row in by_file[file_name]]
        file_rows.append({
            'file': file_name,
            'decl_count': len(lexical_vals),
            'lexical_score_total': round(sum(lexical_vals), 3),
            'lexical_score_mean': round(statistics.fmean(lexical_vals) if lexical_vals else 0.0, 3),
            'lexical_score_max': round(max(lexical_vals) if lexical_vals else 0.0, 3),
            'hybrid_score_total': round(sum(hybrid_vals), 3),
            'hybrid_score_mean': round(statistics.fmean(hybrid_vals) if hybrid_vals else 0.0, 3),
            'hybrid_score_max': round(max(hybrid_vals) if hybrid_vals else 0.0, 3),
        })
    return {'decl_count': len(rows), 'file_count': len(by_file), 'files': file_rows}


def render_md(generated_at: str, targets: list[str], summary: dict[str, Any], top_rows: list[DeclDebtRow], coverage: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append('# Hypothesis Debt Index')
    lines.append('')
    lines.append(f"- generated_at: `{generated_at}`")
    lines.append(f"- declarations_scored: `{summary['decl_count']}`")
    lines.append(f"- files_scored: `{summary['file_count']}`")
    lines.append(f"- graph_anchor_coverage: `{coverage['anchored_rows']}/{coverage['total_rows']}` ({coverage['coverage']})")
    lines.append(f"- nonexported_included: `{coverage['include_nonexported']}`")
    lines.append('')
    lines.append('## Target Files')
    lines.append('')
    for target in targets:
        lines.append(f"- `{target}`")
    lines.append('')
    lines.append('## File Summary')
    lines.append('')
    lines.append('| file | decl_count | lexical_total | lexical_mean | lexical_max | hybrid_total | hybrid_mean | hybrid_max |')
    lines.append('| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |')
    for row in summary['files']:
        lines.append(f"| `{row['file']}` | {row['decl_count']} | {row['lexical_score_total']} | {row['lexical_score_mean']} | {row['lexical_score_max']} | {row['hybrid_score_total']} | {row['hybrid_score_mean']} | {row['hybrid_score_max']} |")
    lines.append('')
    lines.append('## Top Debt Surfaces')
    lines.append('')
    lines.append('| rank | hybrid | lexical | visibility | graph_role | theorem_users | value_users | type_users | rep_layer | declaration | location | h_names | bridge_types | prop_types | predicates |')
    lines.append('| ---: | ---: | ---: | --- | --- | ---: | ---: | ---: | --- | --- | --- | ---: | ---: | ---: | ---: |')
    for idx, row in enumerate(top_rows, start=1):
        lines.append(f"| {idx} | {row.hybrid_score} | {row.score} | `{row.visibility}` | `{row.structural_role}` | {row.reverse_theorem_users} | {row.reverse_value_users} | {row.reverse_type_users} | `{row.rep_layer or '-'}` | `{row.name}` | `{row.file}:{row.line}` | {row.hypothesis_name_vars} | {row.bridge_type_vars} | {row.prop_type_vars} | {row.predicate_type_vars} |")
    lines.append('')
    lines.append('Lexical hint score: `3*hypothesis_names + 2*prop_types + 4*bridge_types + 1*predicate_types + 0.5*instances + 0.1*implicit`.')
    lines.append('Hybrid priority is lexical debt reweighted by DAG-backed structural role and load-bearing score.')
    lines.append('Strict graph doctrine: by default, private/protected non-exported declarations are skipped because they are not graph-addressable theorem surfaces.')
    lines.append('')
    return '\n'.join(lines)


def main() -> int:
    args = parse_args()
    root = repo_root().resolve()
    targets = load_targets(root, list(args.targets))
    rows = collect_rows(root, targets, include_nonexported=args.include_nonexported)
    decl_key_to_full, graph_profiles = load_decl_graph(root)
    anchored = enrich_rows_with_graph(rows, decl_key_to_full, graph_profiles)
    if anchored < len(rows) and not args.allow_heuristic_only:
        missing = len(rows) - anchored
        raise SystemExit(f"[hypothesis-debt] missing graph anchors for {missing}/{len(rows)} declarations; rerun DAG index refresh, widen graph export, or pass --allow-heuristic-only")

    rows.sort(key=lambda row: (-row.hybrid_score, -row.score, row.file, row.line, row.name))
    summary = summarize(rows)
    top_rows = rows[: max(args.top, 0)]
    generated_at = datetime.now(timezone.utc).isoformat(timespec='seconds')
    coverage = {
        'anchored_rows': anchored,
        'total_rows': len(rows),
        'coverage': round((anchored / len(rows)) if rows else 1.0, 6),
        'include_nonexported': bool(args.include_nonexported),
    }

    payload = {
        'generated_at': generated_at,
        'targets': [str(path.resolve().relative_to(root)) for path in targets],
        'summary': summary,
        'graph_anchors': coverage,
        'top': [asdict(row) for row in top_rows],
        'rows': [asdict(row) for row in rows],
    }

    json_out = normalize_target_path(root, args.json_out)
    md_out = normalize_target_path(root, args.md_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    md_out.write_text(render_md(generated_at, payload['targets'], summary, top_rows, coverage), encoding='utf-8')
    def _display(path: Path) -> str:
        try:
            return str(path.relative_to(root))
        except ValueError:
            return str(path)

    print(f"[hypothesis-debt] wrote {_display(json_out)}")
    print(f"[hypothesis-debt] wrote {_display(md_out)}")
    print(f"[hypothesis-debt] scored declarations={summary['decl_count']} files={summary['file_count']}")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
