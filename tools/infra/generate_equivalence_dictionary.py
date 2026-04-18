#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict, deque
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import lean_root, normalize_user_path, repo_root
else:
    from tools.pathing import lean_root, normalize_user_path, repo_root


DEFAULT_JSON_OUT = "reports/dag/equivalence-dictionary.json"
DEFAULT_MD_OUT = "reports/dag/equivalence-dictionary.md"
DEFAULT_CURATED_JSON = "docs/NameEquivalenceRegistry.json"
DECL_RE = re.compile(r"^\s*(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
LEADING_IDENT_RE = re.compile(r"^\s*[\(\[\{¬~\-]*\s*([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)")
RESERVED_HEADS = {
    "by",
    "if",
    "then",
    "else",
    "let",
    "have",
    "show",
    "from",
    "match",
    "fun",
    "forall",
    "where",
    "True",
    "False",
}
SKIP_ALIAS_RHS = {"by", "fun", "match", "if", "let", "show", "calc", "have"}
COMMON_LOCAL_HEADS = {
    "x",
    "y",
    "z",
    "u",
    "v",
    "w",
    "a",
    "b",
    "c",
    "d",
    "e",
    "f",
    "g",
    "h",
    "i",
    "j",
    "k",
    "m",
    "n",
    "p",
    "q",
    "r",
    "s",
    "t",
    "A",
    "B",
    "C",
    "D",
    "E",
    "F",
    "G",
    "H",
    "I",
    "J",
    "K",
    "L",
    "M",
    "N",
    "P",
    "Q",
    "R",
    "S",
    "T",
    "U",
    "V",
    "W",
    "X",
    "Y",
    "Z",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build a maintained equivalence dictionary for Lean declaration surfaces "
            "(variables/functions/lemmas/theorems) from alias and equality/iff relations."
        )
    )
    parser.add_argument(
        "--lean-root",
        default=str((lean_root() / "InfoGeometry").relative_to(repo_root())),
        help="Lean source root to scan (default: lean/InfoGeometry).",
    )
    parser.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", default=DEFAULT_MD_OUT)
    parser.add_argument(
        "--curated-json",
        default=DEFAULT_CURATED_JSON,
        help=(
            "Optional curated alias/equivalence registry JSON merged with auto-extracted relations "
            "(default: docs/NameEquivalenceRegistry.json)."
        ),
    )
    parser.add_argument(
        "--skip-curated",
        action="store_true",
        help="Skip loading curated registry relations.",
    )
    parser.add_argument(
        "--max-header-lines",
        type=int,
        default=40,
        help="Maximum lines to capture for a declaration header before giving up.",
    )
    parser.add_argument("--top-components", type=int, default=40)
    parser.add_argument("--top-unresolved", type=int, default=60)
    return parser.parse_args()


def now_utc_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def module_name_from_path(path: Path, root: Path) -> str:
    rel = path.resolve().relative_to(root.resolve())
    if rel.suffix == ".lean":
        rel = rel.with_suffix("")
    return ".".join(rel.parts)


def qualify_name(name: str, module: str, namespace_stack: list[str]) -> str:
    if "." in name:
        return name
    if namespace_stack:
        return f"{namespace_stack[-1]}.{name}"
    return f"{module}.{name}" if module else name


def push_namespace(module: str, namespace_stack: list[str], raw_ns: str) -> None:
    if "." in raw_ns:
        if raw_ns.startswith("InfoGeometry"):
            namespace_stack.append(raw_ns)
            return
        if namespace_stack:
            namespace_stack.append(f"{namespace_stack[-1]}.{raw_ns}")
            return
        namespace_stack.append(f"{module}.{raw_ns}" if module else raw_ns)
        return
    if namespace_stack:
        namespace_stack.append(f"{namespace_stack[-1]}.{raw_ns}")
    else:
        namespace_stack.append(f"{module}.{raw_ns}" if module else raw_ns)


def pop_namespace(namespace_stack: list[str], raw_end: str | None) -> None:
    if not namespace_stack:
        return
    if not raw_end:
        namespace_stack.pop()
        return
    target = raw_end.strip()
    for i in range(len(namespace_stack) - 1, -1, -1):
        if namespace_stack[i].endswith(target):
            del namespace_stack[i:]
            return
    namespace_stack.pop()


def find_top_level_colon(text: str) -> int | None:
    depth = 0
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            nxt = text[i + 1] if i + 1 < len(text) else ""
            if nxt == "=":
                i += 1
                continue
            return i
        i += 1
    return None


def split_top_level_op(text: str, op: str) -> tuple[str, str] | None:
    depth = 0
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0:
            if op == "↔" and ch == "↔":
                lhs = text[:i].strip()
                rhs = text[i + 1 :].strip()
                if lhs and rhs:
                    return lhs, rhs
            elif op == "=" and ch == "=":
                prev = text[i - 1] if i > 0 else ""
                nxt = text[i + 1] if i + 1 < len(text) else ""
                if prev in {":", "<", ">", "!", "="} or nxt == "=":
                    i += 1
                    continue
                lhs = text[:i].strip()
                rhs = text[i + 1 :].strip()
                if lhs and rhs:
                    return lhs, rhs
        i += 1
    return None


def leading_identifier(expr: str) -> str | None:
    m = LEADING_IDENT_RE.match(expr)
    if not m:
        return None
    token = m.group(1)
    if token in RESERVED_HEADS:
        return None
    return token


def first_identifier(expr: str) -> str | None:
    for m in IDENT_RE.finditer(expr):
        token = m.group(0)
        if token in RESERVED_HEADS:
            continue
        return token
    return None


def short_name(name: str) -> str:
    return name.split(".")[-1]


def resolve_head(head: str | None, global_short_index: dict[str, set[str]]) -> str | None:
    if not head:
        return None
    if "." in head:
        return head
    choices = global_short_index.get(head, set())
    if len(choices) == 1:
        return next(iter(choices))
    return None


def resolve_head_with_status(
    head: str | None, global_short_index: dict[str, set[str]]
) -> tuple[str | None, str]:
    if not head:
        return None, "none"
    if "." in head:
        return head, "resolved_qualified"
    choices = global_short_index.get(head, set())
    if len(choices) == 1:
        return next(iter(choices)), "resolved_unique"
    if len(choices) > 1:
        return None, "ambiguous"
    return None, "missing"


def is_probable_local_head(token: str) -> bool:
    if not token or "." in token:
        return False
    base = token.rstrip("'")
    if not base:
        return True
    if base in COMMON_LOCAL_HEADS:
        return True
    if len(base) == 1:
        return True
    if len(base) <= 2 and base.isalpha():
        return True
    if re.fullmatch(r"[a-z][0-9]*", base):
        return True
    return False


def parse_decl_header(
    lines: list[str], start_idx: int, max_header_lines: int
) -> tuple[str, str, int]:
    header_lines: list[str] = [lines[start_idx].rstrip("\n")]
    i = start_idx + 1
    while i < len(lines) and len(header_lines) < max_header_lines:
        joined = " ".join(header_lines)
        if ":=" in joined:
            break
        header_lines.append(lines[i].rstrip("\n"))
        i += 1
    header = " ".join(x.strip() for x in header_lines if x.strip())
    if ":=" in header:
        prefix, rhs = header.split(":=", 1)
        return prefix.strip(), rhs.strip(), i
    return header.strip(), "", i


def normalize_curated_path(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except Exception:
        return path.as_posix()


def load_curated_relations(curated_json: Path, root: Path) -> list[dict[str, Any]]:
    rel_path = normalize_curated_path(curated_json, root)
    try:
        raw = json.loads(curated_json.read_text(encoding="utf-8"))
    except Exception as ex:
        raise SystemExit(f"[equivalence-dictionary] failed to read curated registry {curated_json}: {ex}") from ex

    payload: Any = raw
    if isinstance(payload, dict):
        payload = payload.get("pairs", [])
    if not isinstance(payload, list):
        raise SystemExit(
            "[equivalence-dictionary] curated registry must be a list or an object with `pairs` list: "
            f"{curated_json}"
        )

    rows: list[dict[str, Any]] = []
    errors: list[str] = []
    for idx, item in enumerate(payload, start=1):
        lhs = ""
        rhs = ""
        relation_kind = "curated_alias"
        note = ""
        source = "curated"

        if isinstance(item, dict):
            lhs = str(item.get("lhs", "")).strip()
            rhs = str(item.get("rhs", "")).strip()
            relation_kind = str(item.get("relationKind", relation_kind)).strip() or relation_kind
            note = str(item.get("note", "")).strip()
            source = str(item.get("source", source)).strip() or source
        elif isinstance(item, list) and len(item) == 2:
            lhs = str(item[0]).strip()
            rhs = str(item[1]).strip()
        else:
            errors.append(f"entry {idx}: expected object {{lhs,rhs,...}} or [lhs, rhs]")
            continue

        if not lhs or not rhs:
            errors.append(f"entry {idx}: both lhs and rhs are required")
            continue

        row: dict[str, Any] = {
            "decl": f"curated::{idx}",
            "declKind": "curated",
            "relationKind": relation_kind,
            "lhsExpr": lhs,
            "rhsExpr": rhs,
            "lhsHeadRaw": lhs,
            "rhsHeadRaw": rhs,
            "file": rel_path,
            "line": idx,
            "source": source,
        }
        if note:
            row["note"] = note
        rows.append(row)

    if errors:
        detail = "\n".join(f"  - {x}" for x in errors)
        raise SystemExit(
            "[equivalence-dictionary] invalid curated registry rows in "
            f"{curated_json}:\n{detail}"
        )
    return rows


def scan_lean_files(lean_src_root: Path, max_header_lines: int) -> dict[str, Any]:
    declarations: list[dict[str, Any]] = []
    relations: list[dict[str, Any]] = []
    parse_failures: list[dict[str, Any]] = []
    files = sorted(lean_src_root.rglob("*.lean"))

    for path in files:
        module = module_name_from_path(path, lean_src_root.parent)
        rel_path = path.resolve().relative_to(repo_root().resolve()).as_posix()
        try:
            lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
        except Exception as ex:
            parse_failures.append({"file": rel_path, "error": f"read-error: {ex}"})
            continue

        namespace_stack: list[str] = []
        i = 0
        while i < len(lines):
            line = lines[i]
            ns = NAMESPACE_RE.match(line)
            if ns:
                push_namespace(module, namespace_stack, ns.group(1))
                i += 1
                continue
            en = END_RE.match(line)
            if en:
                pop_namespace(namespace_stack, en.group(1))
                i += 1
                continue

            dm = DECL_RE.match(line)
            if not dm:
                i += 1
                continue

            decl_kind = dm.group(1)
            decl_name = dm.group(2)
            fq_decl = qualify_name(decl_name, module, namespace_stack)
            prefix, rhs, next_i = parse_decl_header(lines, i, max_header_lines)

            after_name = prefix.split(decl_name, 1)[1] if decl_name in prefix else ""
            colon_idx = find_top_level_colon(after_name)
            statement = ""
            if colon_idx is not None:
                statement = after_name[colon_idx + 1 :].strip()

            declarations.append(
                {
                    "name": fq_decl,
                    "kind": decl_kind,
                    "file": rel_path,
                    "line": i + 1,
                    "module": module,
                    "statement": statement,
                }
            )

            if decl_kind in {"theorem", "lemma"} and statement:
                relation_kind = ""
                split: tuple[str, str] | None = split_top_level_op(statement, "↔")
                if split is not None:
                    relation_kind = "iff"
                else:
                    split = split_top_level_op(statement, "=")
                    if split is not None:
                        relation_kind = "eq"
                if split is not None:
                    lhs_expr, rhs_expr = split
                    relations.append(
                        {
                            "decl": fq_decl,
                            "declKind": decl_kind,
                            "relationKind": relation_kind,
                            "lhsExpr": lhs_expr,
                            "rhsExpr": rhs_expr,
                            "lhsHeadRaw": first_identifier(lhs_expr),
                            "rhsHeadRaw": first_identifier(rhs_expr),
                            "file": rel_path,
                            "line": i + 1,
                            "source": "auto",
                        }
                    )

            if decl_kind in {"def", "abbrev"} and rhs:
                rhs_head = leading_identifier(rhs)
                if rhs_head and rhs_head not in SKIP_ALIAS_RHS:
                    relations.append(
                        {
                            "decl": fq_decl,
                            "declKind": decl_kind,
                            "relationKind": "alias",
                            "lhsExpr": decl_name,
                            "rhsExpr": rhs.strip(),
                            "lhsHeadRaw": decl_name,
                            "rhsHeadRaw": rhs_head,
                            "file": rel_path,
                            "line": i + 1,
                            "source": "auto",
                        }
                    )

            i = next_i

    return {
        "files": files,
        "declarations": declarations,
        "relations": relations,
        "parseFailures": parse_failures,
    }


def enrich_relations(
    declarations: list[dict[str, Any]],
    relations: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, Counter[str]], dict[str, set[str]]]:
    short_index: dict[str, set[str]] = defaultdict(set)
    for d in declarations:
        fq = str(d["name"])
        short_index[short_name(fq)].add(fq)

    unresolved_all: Counter[str] = Counter()
    unresolved_ambiguous: Counter[str] = Counter()
    unresolved_missing: Counter[str] = Counter()
    unresolved_missing_nonlocal: Counter[str] = Counter()
    enriched: list[dict[str, Any]] = []
    for r in relations:
        lhs_raw = r.get("lhsHeadRaw")
        rhs_raw = r.get("rhsHeadRaw")
        lhs, lhs_status = resolve_head_with_status(lhs_raw, short_index)
        rhs, rhs_status = resolve_head_with_status(rhs_raw, short_index)
        if lhs_raw and lhs is None:
            key = str(lhs_raw)
            unresolved_all[key] += 1
            if lhs_status == "ambiguous":
                unresolved_ambiguous[key] += 1
            elif lhs_status == "missing":
                unresolved_missing[key] += 1
                if not is_probable_local_head(key):
                    unresolved_missing_nonlocal[key] += 1
        if rhs_raw and rhs is None:
            key = str(rhs_raw)
            unresolved_all[key] += 1
            if rhs_status == "ambiguous":
                unresolved_ambiguous[key] += 1
            elif rhs_status == "missing":
                unresolved_missing[key] += 1
                if not is_probable_local_head(key):
                    unresolved_missing_nonlocal[key] += 1
        row = dict(r)
        row["lhsHead"] = lhs
        row["rhsHead"] = rhs
        row["lhsStatus"] = lhs_status
        row["rhsStatus"] = rhs_status
        row["isResolvedPair"] = bool(lhs and rhs)
        enriched.append(row)
    return (
        enriched,
        {
            "all": unresolved_all,
            "ambiguous": unresolved_ambiguous,
            "missing": unresolved_missing,
            "missingNonlocal": unresolved_missing_nonlocal,
        },
        short_index,
    )


def build_components(relations: list[dict[str, Any]]) -> list[dict[str, Any]]:
    graph: dict[str, set[str]] = defaultdict(set)
    edge_meta: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)

    for r in relations:
        lhs = r.get("lhsHead")
        rhs = r.get("rhsHead")
        if not lhs or not rhs or lhs == rhs:
            continue
        a, b = sorted((lhs, rhs))
        graph[a].add(b)
        graph[b].add(a)
        edge_meta[(a, b)].append(r)

    seen: set[str] = set()
    components: list[dict[str, Any]] = []
    cid = 1
    for node in sorted(graph):
        if node in seen:
            continue
        q: deque[str] = deque([node])
        seen.add(node)
        members: list[str] = []
        while q:
            cur = q.popleft()
            members.append(cur)
            for nxt in sorted(graph[cur]):
                if nxt in seen:
                    continue
                seen.add(nxt)
                q.append(nxt)
        members.sort()
        local_edges: list[tuple[str, str]] = []
        relation_kind_counter: Counter[str] = Counter()
        sample_decls: list[str] = []
        for i, a in enumerate(members):
            for b in members[i + 1 :]:
                key = (a, b)
                rels = edge_meta.get(key)
                if not rels:
                    continue
                local_edges.append(key)
                for r in rels:
                    relation_kind_counter[str(r.get("relationKind", "unknown"))] += 1
                    if len(sample_decls) < 10:
                        sample_decls.append(str(r.get("decl", "")))
        components.append(
            {
                "id": f"EQC-{cid:04d}",
                "size": len(members),
                "members": members,
                "edgeCount": len(local_edges),
                "relationKinds": dict(relation_kind_counter),
                "sampleDecls": sample_decls,
            }
        )
        cid += 1

    components.sort(key=lambda row: (-int(row["size"]), -int(row["edgeCount"]), row["id"]))
    return components


def render_markdown(
    payload: dict[str, Any], top_components: int, top_unresolved: int
) -> str:
    summary = payload.get("summary", {})
    lines: list[str] = []
    lines.append("# Equivalence Dictionary")
    lines.append("")
    lines.append(
        "Maintained dictionary of equivalent naming surfaces extracted from Lean source. "
        "It combines theorem/lemma `=` and `↔` relations with `def`/`abbrev` alias surfaces."
    )
    lines.append("")
    lines.append("## Summary")
    for key in [
        "lean_file_count",
        "declaration_count",
        "auto_relation_count",
        "curated_relation_count",
        "relation_count",
        "resolved_pair_count",
        "unresolved_head_token_total_raw",
        "unresolved_head_unique_count_raw",
        "unresolved_head_token_total",
        "unresolved_head_unique_count",
        "unresolved_ambiguous_token_total",
        "unresolved_ambiguous_unique_count",
        "unresolved_missing_token_total",
        "unresolved_missing_unique_count",
        "unresolved_missing_nonlocal_token_total",
        "unresolved_missing_nonlocal_unique_count",
        "component_count",
        "parse_failure_count",
    ]:
        lines.append(f"- `{key}`: `{summary.get(key, 0)}`")
    curated = payload.get("curated", {})
    if curated:
        lines.append(f"- `curated_registry`: `{curated.get('path', '-')}`")
        lines.append(f"- `curated_enabled`: `{curated.get('enabled', False)}`")
    lines.append("")
    lines.append("## Update Command")
    lines.append("```bash")
    lines.append(
        "python3 tools/infra/generate_equivalence_dictionary.py "
        "--curated-json docs/NameEquivalenceRegistry.json "
        "--json-out reports/dag/equivalence-dictionary.json "
        "--md-out reports/dag/equivalence-dictionary.md"
    )
    lines.append("```")
    lines.append("")
    lines.append("## Largest Equivalence Components")
    comps = payload.get("components", [])[:top_components]
    if comps:
        for c in comps:
            lines.append(
                f"- `{c.get('id')}` size `{c.get('size')}` edges `{c.get('edgeCount')}` "
                f"relationKinds `{c.get('relationKinds')}`"
            )
            members = c.get("members", [])
            preview = ", ".join(f"`{m}`" for m in members[:12])
            if preview:
                lines.append(f"  members: {preview}")
            samples = c.get("sampleDecls", [])
            if samples:
                lines.append("  sample declarations:")
                for decl in samples[:5]:
                    lines.append(f"  - `{decl}`")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Unresolved Head Tokens")
    unresolved = payload.get("unresolvedHeads", [])[:top_unresolved]
    if unresolved:
        for row in unresolved:
            lines.append(f"- `{row.get('head')}`: `{row.get('count')}`")
    else:
        lines.append("- none")
    lines.append("")
    lines.append("## Notes")
    lines.append("- This report is lexical and intentionally conservative.")
    lines.append("- For closure promotion, pair it with translation-registry and architecture audits.")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    root = repo_root()
    lean_src_root = normalize_user_path(args.lean_root, lean_root() / "InfoGeometry")
    json_out = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, root / DEFAULT_MD_OUT)
    curated_json = normalize_user_path(args.curated_json, root / DEFAULT_CURATED_JSON)

    if not lean_src_root.exists():
        raise SystemExit(f"lean root not found: {lean_src_root}")

    scan = scan_lean_files(lean_src_root, args.max_header_lines)
    declarations = scan["declarations"]
    relations_raw = list(scan["relations"])

    curated_relations: list[dict[str, Any]] = []
    curated_warnings: list[str] = []
    curated_enabled = not args.skip_curated
    if curated_enabled:
        if curated_json.exists():
            curated_relations = load_curated_relations(curated_json, root)
            relations_raw.extend(curated_relations)
        else:
            curated_warnings.append(f"missing curated registry: {curated_json}")

    relations, unresolved_counters, _ = enrich_relations(declarations, relations_raw)
    components = build_components(relations)

    unresolved_all_counter = Counter(
        {head: count for head, count in unresolved_counters["all"].items() if head not in {"Eq", "Iff"}}
    )
    unresolved_ambiguous_counter = Counter(
        {head: count for head, count in unresolved_counters["ambiguous"].items() if head not in {"Eq", "Iff"}}
    )
    unresolved_missing_counter = Counter(
        {head: count for head, count in unresolved_counters["missing"].items() if head not in {"Eq", "Iff"}}
    )
    unresolved_missing_nonlocal_counter = Counter(
        {
            head: count
            for head, count in unresolved_counters["missingNonlocal"].items()
            if head not in {"Eq", "Iff"}
        }
    )

    # Signal-oriented unresolved surface: ambiguous internal heads only.
    unresolved_counter = unresolved_ambiguous_counter
    unresolved_heads = [
        {"head": head, "count": count}
        for head, count in unresolved_counter.most_common()
    ]
    unresolved_heads_raw = [
        {"head": head, "count": count}
        for head, count in unresolved_all_counter.most_common()
    ]
    unresolved_total = sum(unresolved_counter.values())
    unresolved_total_raw = sum(unresolved_all_counter.values())
    resolved_pair_count = sum(1 for r in relations if r.get("isResolvedPair"))
    parse_failures = list(scan["parseFailures"])

    payload: dict[str, Any] = {
        "kind": "equivalence_dictionary",
        "generatedAtUTC": now_utc_iso(),
        "leanRoot": str(lean_src_root.resolve()),
        "summary": {
            "lean_file_count": len(scan["files"]),
            "declaration_count": len(declarations),
            "auto_relation_count": len(scan["relations"]),
            "curated_relation_count": len(curated_relations),
            "relation_count": len(relations),
            "resolved_pair_count": resolved_pair_count,
            "unresolved_head_token_total_raw": unresolved_total_raw,
            "unresolved_head_unique_count_raw": len(unresolved_heads_raw),
            "unresolved_head_token_total": unresolved_total,
            "unresolved_head_unique_count": len(unresolved_heads),
            "unresolved_ambiguous_token_total": sum(unresolved_ambiguous_counter.values()),
            "unresolved_ambiguous_unique_count": len(unresolved_ambiguous_counter),
            "unresolved_missing_token_total": sum(unresolved_missing_counter.values()),
            "unresolved_missing_unique_count": len(unresolved_missing_counter),
            "unresolved_missing_nonlocal_token_total": sum(unresolved_missing_nonlocal_counter.values()),
            "unresolved_missing_nonlocal_unique_count": len(unresolved_missing_nonlocal_counter),
            "component_count": len(components),
            "parse_failure_count": len(parse_failures),
        },
        "curated": {
            "enabled": curated_enabled,
            "path": normalize_curated_path(curated_json, root),
            "relationCount": len(curated_relations),
            "warnings": curated_warnings,
        },
        "components": components,
        "unresolvedHeads": unresolved_heads,
        "unresolvedHeadsRaw": unresolved_heads_raw,
        "relations": relations,
        "parseFailures": parse_failures,
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    md_out.write_text(
        render_markdown(payload, top_components=args.top_components, top_unresolved=args.top_unresolved),
        encoding="utf-8",
    )

    print(
        "[equivalence-dictionary] "
        f"files={payload['summary']['lean_file_count']} "
        f"decls={payload['summary']['declaration_count']} "
        f"autoRelations={payload['summary']['auto_relation_count']} "
        f"curatedRelations={payload['summary']['curated_relation_count']} "
        f"relations={payload['summary']['relation_count']} "
        f"components={payload['summary']['component_count']} "
        f"resolvedPairs={payload['summary']['resolved_pair_count']} "
        f"unresolvedTotal={payload['summary']['unresolved_head_token_total']}"
    )
    print(f"[equivalence-dictionary] wrote {json_out}")
    print(f"[equivalence-dictionary] wrote {md_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
