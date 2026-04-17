#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict, deque
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import (
        default_decl_metadata_file,
        default_decl_index_dir,
        normalize_user_path,
        repo_root,
    )
else:
    from tools.pathing import (
        default_decl_metadata_file,
        default_decl_index_dir,
        normalize_user_path,
        repo_root,
    )


ROOT = repo_root()
DEFAULT_JSON_OUT = "reports/dag/functorial-invariance-audit.json"
DEFAULT_MD_OUT = "reports/dag/functorial-invariance-audit.md"
DEFAULT_REP_TAGS = "artifacts/dag/representation-depth-tags.json"
CORRIDOR_TOKENS = ("equiv", "iso", "isomorph", "simplex", "projective")


@dataclass(frozen=True)
class Corridor:
    root_decl: str
    root_file: str
    canopy_decl: str
    canopy_file: str
    depth: int
    path: list[str]


def rel(path_str: str) -> str:
    p = Path(path_str)
    if p.is_absolute():
        try:
            return p.resolve().relative_to(ROOT.resolve()).as_posix()
        except Exception:
            return p.as_posix()
    return p.as_posix()


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            raw = json.loads(line)
            if isinstance(raw, dict):
                rows.append(raw)
    return rows


def has_rep_depth(attrs: Any) -> bool:
    if not isinstance(attrs, list):
        return False
    return any("rep_depth" in str(a) for a in attrs)


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Trace functorial Core->canopy connectivity and isomorphism corridors "
            "to prevent false 'foundational void' audits."
        )
    )
    ap.add_argument(
        "--decls",
        default=str(default_decl_metadata_file().relative_to(ROOT)),
        help="Path to decls.jsonl metadata",
    )
    ap.add_argument(
        "--edges",
        default=str((default_decl_index_dir() / "edges.jsonl").relative_to(ROOT)),
        help="Path to edges.jsonl dependency edges",
    )
    ap.add_argument(
        "--rep-tags",
        default=DEFAULT_REP_TAGS,
        help=(
            "Optional representation-depth tag snapshot "
            "(artifacts/dag/representation-depth-tags.json)"
        ),
    )
    ap.add_argument(
        "--root-prefix",
        action="append",
        default=[],
        help="Repeatable declaration-root file prefix for foundational roots",
    )
    ap.add_argument(
        "--canopy-prefix",
        action="append",
        default=[],
        help="Repeatable file prefix for canopy declarations",
    )
    ap.add_argument(
        "--edge-kind",
        action="append",
        default=[],
        help="Edge kinds to use (repeatable). Defaults to value+type.",
    )
    ap.add_argument("--max-depth", type=int, default=8, help="Max reverse-path depth")
    ap.add_argument("--top", type=int, default=30, help="Top rows in markdown tables")
    ap.add_argument("--json-out", default=DEFAULT_JSON_OUT)
    ap.add_argument("--md-out", default=DEFAULT_MD_OUT)
    return ap.parse_args()


def load_rep_tagged_names(path: Path) -> set[str]:
    if not path.exists():
        return set()
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return set()
    if not isinstance(raw, dict):
        return set()
    rows = raw.get("declarations")
    if not isinstance(rows, list):
        return set()
    out: set[str] = set()
    for row in rows:
        if not isinstance(row, dict):
            continue
        name = str(row.get("name", "")).strip()
        if name:
            out.add(name)
    return out


def shortest_path_to_canopy(
    start: str,
    reverse_adj: dict[str, list[str]],
    canopy_names: set[str],
    *,
    max_depth: int,
) -> tuple[str, list[str]] | None:
    q: deque[tuple[str, int]] = deque([(start, 0)])
    parent: dict[str, str | None] = {start: None}
    while q:
        node, depth = q.popleft()
        if node in canopy_names and node != start:
            path: list[str] = []
            cur: str | None = node
            while cur is not None:
                path.append(cur)
                cur = parent[cur]
            path.reverse()
            return node, path
        if depth >= max_depth:
            continue
        for nxt in reverse_adj.get(node, []):
            if nxt in parent:
                continue
            parent[nxt] = node
            q.append((nxt, depth + 1))
    return None


def main() -> int:
    args = parse_args()
    decls_path = normalize_user_path(args.decls, default_decl_metadata_file())
    edges_path = normalize_user_path(args.edges, default_decl_index_dir() / "edges.jsonl")
    rep_tags_path = normalize_user_path(args.rep_tags, ROOT / DEFAULT_REP_TAGS)
    json_out = normalize_user_path(args.json_out, ROOT / DEFAULT_JSON_OUT)
    md_out = normalize_user_path(args.md_out, ROOT / DEFAULT_MD_OUT)

    if args.root_prefix:
        root_prefixes = tuple(args.root_prefix)
    else:
        root_prefixes = (
            "lean/InfoGeometry/Core/",
            "lean/InfoGeometry/MaxEnt/",
            "lean/InfoGeometry/Convex/",
            "lean/InfoGeometry/Geometry/",
        )
    if args.canopy_prefix:
        canopy_prefixes = tuple(args.canopy_prefix)
    else:
        canopy_prefixes = (
            "lean/InfoGeometry/Canonical/",
            "lean/InfoGeometry/Thermo/",
            "lean/InfoGeometry/Thermodynamics/",
        )

    edge_kinds = set(args.edge_kind) if args.edge_kind else {"value", "type"}

    decl_rows = load_jsonl(decls_path)
    edge_rows = load_jsonl(edges_path)
    rep_tagged_names = load_rep_tagged_names(rep_tags_path)

    decl_by_name: dict[str, dict[str, Any]] = {}
    for row in decl_rows:
        name = str(row.get("name", ""))
        if not name:
            continue
        copied = dict(row)
        copied["file_rel"] = rel(str(row.get("file", "")))
        decl_by_name[name] = copied

    reverse_adj: dict[str, list[str]] = defaultdict(list)
    used_edge_count = 0
    for row in edge_rows:
        kind = str(row.get("kind", ""))
        if kind not in edge_kinds:
            continue
        src = str(row.get("src", ""))
        dst = str(row.get("dst", ""))
        if not src or not dst:
            continue
        if src not in decl_by_name or dst not in decl_by_name:
            continue
        reverse_adj[dst].append(src)
        used_edge_count += 1

    root_decls = [
        name
        for name, row in decl_by_name.items()
        if any(str(row.get("file_rel", "")).startswith(p) for p in root_prefixes)
    ]
    canopy_decls = {
        name
        for name, row in decl_by_name.items()
        if any(str(row.get("file_rel", "")).startswith(p) for p in canopy_prefixes)
    }

    tag_source = "representation_depth_tags" if rep_tagged_names else "decl_attrs"
    if rep_tagged_names:
        root_tagged = [n for n in root_decls if n in rep_tagged_names]
    else:
        root_tagged = [n for n in root_decls if has_rep_depth(decl_by_name[n].get("attrs"))]
    root_untagged = [n for n in root_decls if n not in set(root_tagged)]

    corridors: list[Corridor] = []
    roots_with_canopy = 0
    untagged_with_canopy = 0
    roots_by_file = Counter()
    roots_with_canopy_by_file = Counter()
    iso_corridor_count = 0
    simplex_projective_count = 0

    for root_decl in root_decls:
        row = decl_by_name[root_decl]
        root_file = str(row.get("file_rel", ""))
        roots_by_file[root_file] += 1
        sp = shortest_path_to_canopy(
            root_decl,
            reverse_adj,
            canopy_decls,
            max_depth=max(1, args.max_depth),
        )
        if sp is None:
            continue
        roots_with_canopy += 1
        roots_with_canopy_by_file[root_file] += 1
        if root_decl in root_untagged:
            untagged_with_canopy += 1
        canopy_decl, path = sp
        canopy_file = str(decl_by_name[canopy_decl].get("file_rel", ""))
        depth = max(0, len(path) - 1)
        c = Corridor(
            root_decl=root_decl,
            root_file=root_file,
            canopy_decl=canopy_decl,
            canopy_file=canopy_file,
            depth=depth,
            path=path,
        )
        corridors.append(c)
        corridor_text = " ".join(path).lower()
        if any(tok in corridor_text for tok in CORRIDOR_TOKENS):
            iso_corridor_count += 1
        if ("simplex" in corridor_text) or ("projective" in corridor_text):
            simplex_projective_count += 1

    corridors.sort(key=lambda c: (c.depth, c.root_decl, c.canopy_decl))
    canopy_reached = len({c.canopy_decl for c in corridors})

    status = "PASS"
    failures: list[str] = []
    if roots_with_canopy == 0:
        status = "FAIL"
        failures.append("no_core_to_canopy_functorial_paths")
    if iso_corridor_count == 0:
        status = "FAIL"
        failures.append("no_isomorphism_corridors_detected")
    if simplex_projective_count == 0:
        status = "FAIL"
        failures.append("no_simplex_or_projective_corridors_detected")

    summary = {
        "schema": "ig.functorial-invariance-audit.v1",
        "status": status,
        "failures": failures,
        "inputs": {
            "decls": rel(str(decls_path)),
            "edges": rel(str(edges_path)),
            "rep_tags": rel(str(rep_tags_path)),
            "tag_source": tag_source,
            "edge_kinds": sorted(edge_kinds),
            "root_prefixes": list(root_prefixes),
            "canopy_prefixes": list(canopy_prefixes),
            "max_depth": int(args.max_depth),
        },
        "counts": {
            "decl_total": len(decl_by_name),
            "root_decl_total": len(root_decls),
            "root_tagged_total": len(root_tagged),
            "root_untagged_total": len(root_untagged),
            "root_with_canopy_total": roots_with_canopy,
            "root_untagged_with_canopy_total": untagged_with_canopy,
            "canopy_decl_total": len(canopy_decls),
            "canopy_reached_total": canopy_reached,
            "corridor_total": len(corridors),
            "isomorphism_corridor_total": iso_corridor_count,
            "simplex_projective_corridor_total": simplex_projective_count,
            "used_edge_total": used_edge_count,
        },
        "top_root_files": [
            {
                "file": f,
                "root_decl_count": int(roots_by_file[f]),
                "root_with_canopy_count": int(roots_with_canopy_by_file[f]),
            }
            for f, _ in roots_by_file.most_common(args.top)
        ],
        "corridor_samples": [asdict(c) for c in corridors[: args.top]],
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    md_lines: list[str] = []
    md_lines.append("# Functorial Invariance Audit")
    md_lines.append("")
    md_lines.append(f"- Status: **{status}**")
    md_lines.append(f"- Root declarations: `{len(root_decls)}`")
    md_lines.append(f"- Root declarations with canopy consumers: `{roots_with_canopy}`")
    md_lines.append(f"- Root declarations with rep-depth tags: `{len(root_tagged)}`")
    md_lines.append(f"- Untagged root declarations: `{len(root_untagged)}`")
    md_lines.append(f"- Untagged root declarations with canopy consumers: `{untagged_with_canopy}`")
    md_lines.append(f"- Isomorphism corridors (equiv/iso/simplex/projective): `{iso_corridor_count}`")
    md_lines.append(f"- Simplex/projective corridors: `{simplex_projective_count}`")
    md_lines.append("")
    md_lines.append("Tag coverage is informational only; PASS/FAIL is decided by")
    md_lines.append("Core→canopy functorial connectivity and corridor checks, not by tag density.")
    if failures:
        md_lines.append("")
        md_lines.append("## Failures")
        for f in failures:
            md_lines.append(f"- `{f}`")
    md_lines.append("")
    md_lines.append("## Root File Coverage")
    md_lines.append("")
    md_lines.append("| File | Root Decls | Reaching Canopy |")
    md_lines.append("|---|---:|---:|")
    for row in summary["top_root_files"]:
        md_lines.append(
            f"| `{row['file']}` | {row['root_decl_count']} | {row['root_with_canopy_count']} |"
        )
    md_lines.append("")
    md_lines.append("## Corridor Samples")
    md_lines.append("")
    md_lines.append("| Root Decl | Canopy Decl | Depth | Root File | Canopy File |")
    md_lines.append("|---|---|---:|---|---|")
    for c in corridors[: args.top]:
        md_lines.append(
            f"| `{c.root_decl}` | `{c.canopy_decl}` | {c.depth} | `{c.root_file}` | `{c.canopy_file}` |"
        )

    md_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    print(f"[functorial-invariance] status={status}")
    print(f"[functorial-invariance] root_decl_total={len(root_decls)}")
    print(f"[functorial-invariance] root_with_canopy_total={roots_with_canopy}")
    print(f"[functorial-invariance] root_untagged_with_canopy_total={untagged_with_canopy}")
    print(f"[functorial-invariance] isomorphism_corridor_total={iso_corridor_count}")
    print(f"[functorial-invariance] simplex_projective_corridor_total={simplex_projective_count}")
    print(f"[functorial-invariance] json={rel(str(json_out))}")
    print(f"[functorial-invariance] md={rel(str(md_out))}")
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
