#!/usr/bin/env python3
"""Generate a socket-debt ledger with ownerless/bridge-backed classification.

This is a derived observability tool. It does not prove anything; it only
organizes the repo's explicit `@[socket_debt_tag]` surfaces so we can see which
ones still need an owner or bridge proof to be plugged in.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List


ROOT = Path(__file__).resolve().parent / "graph_overlay_toolchain" / "graph_overlay" / "scripts"
sys.path.insert(0, str(ROOT))

from lean_graph_overlay import build_graph, decl_nodes, filter_graph_by_prefix  # noqa: E402


def file_role_counts(decls: List[Dict[str, Any]]) -> Dict[str, Dict[str, int]]:
    counts: Dict[str, Dict[str, int]] = defaultdict(lambda: {"owner": 0, "bridge": 0, "socket": 0})
    for d in decls:
        bucket = counts[d["file"]]
        bucket["owner"] += int(bool(d.get("is_owner")))
        bucket["bridge"] += int(bool(d.get("is_bridge")))
        bucket["socket"] += int(bool(d.get("is_socket")))
    return counts


def classify_socket(decl: Dict[str, Any], counts: Dict[str, Dict[str, int]]) -> str:
    file_counts = counts[decl["file"]]
    if file_counts["owner"] == 0 and file_counts["bridge"] == 0:
        return "ownerless_socket"
    return "bridge_backed_socket"


def _tokenize_name(name: str) -> set[str]:
    tokens: set[str] = set()
    for part in re.split(r"[^A-Za-z0-9]+", name):
        if not part:
            continue
        lower = part.lower()
        tokens.add(lower)
        chunks = re.findall(r"[A-Z]?[a-z]+|[0-9]+", part)
        if chunks:
            tokens.update(chunk.lower() for chunk in chunks)
    return tokens


def _impact_score(row: Dict[str, Any]) -> tuple[int, int, int, int]:
    reverse_deps = len(row.get("reverse_dependencies") or [])
    direct_deps = len(row.get("direct_dependencies") or [])
    file_owner_count = row.get("file_owner_count", 0)
    file_bridge_count = row.get("file_bridge_count", 0)
    file_socket_count = row.get("file_socket_count", 0)
    return (reverse_deps, direct_deps, file_owner_count + file_bridge_count, file_socket_count)


def _root_score(row: Dict[str, Any]) -> tuple[int, int, int, int]:
    direct_deps = len(row.get("direct_dependencies") or [])
    file_owner_count = row.get("file_owner_count", 0)
    file_bridge_count = row.get("file_bridge_count", 0)
    file_socket_count = row.get("file_socket_count", 0)
    reverse_deps = len(row.get("reverse_dependencies") or [])
    return (direct_deps, file_owner_count + file_bridge_count, file_socket_count, -reverse_deps)


def _candidate_score(socket_row: Dict[str, Any], candidate: Dict[str, Any]) -> tuple[int, int, int]:
    socket_tokens = _tokenize_name(socket_row["name"]) | _tokenize_name(socket_row["fqname"])
    candidate_tokens = _tokenize_name(candidate["name"]) | _tokenize_name(candidate["fqname"])
    overlap = len(socket_tokens & candidate_tokens)
    if socket_row["file"] == candidate["file"]:
        overlap += 1
    if candidate.get("is_owner"):
        overlap += 2
    if candidate.get("is_bridge"):
        overlap += 1
    return (
        overlap,
        len(candidate.get("reverse_dependencies") or []),
        len(candidate.get("direct_dependencies") or []),
    )


def ranked_ownerless_rows(rows: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    ownerless = [r for r in rows if r["status"] == "ownerless_socket"]
    ownerless.sort(key=lambda r: (_root_score(r)[0], _root_score(r)[1], _root_score(r)[2], _root_score(r)[3], r["fqname"]))
    return ownerless


def impact_ranked_ownerless_rows(rows: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    ownerless = [r for r in rows if r["status"] == "ownerless_socket"]
    ownerless.sort(key=lambda r: (-_impact_score(r)[0], -_impact_score(r)[1], -_impact_score(r)[2], -_impact_score(r)[3], r["fqname"]))
    return ownerless


def local_proof_candidates(graph: Dict[str, Any], rows: List[Dict[str, Any]], *, limit: int = 5) -> Dict[str, List[Dict[str, Any]]]:
    decls = decl_nodes(graph)
    candidates = [d for d in decls if d.get("is_owner") or d.get("is_bridge") or d.get("template_role") in {"Witness", "Source"}]
    out: Dict[str, List[Dict[str, Any]]] = {}
    for row in rows:
        if row["status"] != "ownerless_socket":
            continue
        scored: List[Dict[str, Any]] = []
        for cand in candidates:
            if cand["fqname"] == row["fqname"]:
                continue
            score = _candidate_score(row, cand)
            if score[0] <= 0:
                continue
            scored.append(
                {
                    "fqname": cand["fqname"],
                    "file": cand["file"],
                    "start_line": cand["start_line"],
                    "end_line": cand["end_line"],
                    "is_owner": cand.get("is_owner"),
                    "is_bridge": cand.get("is_bridge"),
                    "template_role": cand.get("template_role"),
                    "score": list(score),
                }
            )
        scored.sort(key=lambda r: (-r["score"][0], -r["score"][1], -r["score"][2], r["fqname"]))
        out[row["fqname"]] = scored[:limit]
    return out


def socket_rows(graph: Dict[str, Any]) -> List[Dict[str, Any]]:
    decls = decl_nodes(graph)
    counts = file_role_counts(decls)
    rows: List[Dict[str, Any]] = []
    for d in decls:
        if not d.get("is_socket"):
            continue
        row = dict(d)
        row["file_owner_count"] = counts[d["file"]]["owner"]
        row["file_bridge_count"] = counts[d["file"]]["bridge"]
        row["file_socket_count"] = counts[d["file"]]["socket"]
        row["status"] = classify_socket(d, counts)
        rows.append(row)
    rows.sort(key=lambda r: (r["status"], r["file"], r["start_line"], r["fqname"]))
    return rows


def write_json(graph: Dict[str, Any], rows: List[Dict[str, Any]], out: Path) -> None:
    payload = {
        "root": graph["root"],
        "root_prefix": graph.get("root_prefix", ""),
        "include_tags": graph.get("include_tags", []),
        "stats": graph["stats"],
        "socket_count": len(rows),
        "ownerless_socket_count": sum(1 for r in rows if r["status"] == "ownerless_socket"),
        "bridge_backed_socket_count": sum(1 for r in rows if r["status"] == "bridge_backed_socket"),
        "sockets": rows,
        "ownerless_ranked": ranked_ownerless_rows(rows),
        "ownerless_impact_ranked": impact_ranked_ownerless_rows(rows),
        "candidate_owner_surfaces": local_proof_candidates(graph, rows),
    }
    out.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def write_markdown(graph: Dict[str, Any], rows: List[Dict[str, Any]], out: Path) -> None:
    lines: List[str] = []
    lines.append("# Socket Debt Ledger")
    lines.append("")
    lines.append(f"Root: `{graph['root']}`")
    if graph.get("root_prefix"):
        lines.append(f"Prefix: `{graph['root_prefix']}`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- socket declarations: **{len(rows)}**")
    lines.append(f"- ownerless sockets: **{sum(1 for r in rows if r['status'] == 'ownerless_socket')}**")
    lines.append(f"- bridge-backed sockets: **{sum(1 for r in rows if r['status'] == 'bridge_backed_socket')}**")
    lines.append("")

    file_summary: Dict[str, Dict[str, int]] = defaultdict(lambda: {"socket": 0, "owner": 0, "bridge": 0, "ownerless": 0})
    for r in rows:
        file_summary[r["file"]]["socket"] += 1
        file_summary[r["file"]]["owner"] += r["file_owner_count"]
        file_summary[r["file"]]["bridge"] += r["file_bridge_count"]
        file_summary[r["file"]]["ownerless"] += int(r["status"] == "ownerless_socket")

    lines.append("## File summary")
    lines.append("")
    lines.append("| file | sockets | owner tags | bridge tags | ownerless sockets |")
    lines.append("| --- | ---: | ---: | ---: | ---: |")
    for file_name, stats in sorted(file_summary.items(), key=lambda kv: (-kv[1]["ownerless"], kv[0])):
        lines.append(
            f"| `{file_name}` | {stats['socket']} | {stats['owner']} | {stats['bridge']} | {stats['ownerless']} |"
        )
    lines.append("")

    def add_table(title: str, subset: List[Dict[str, Any]]) -> None:
        lines.append(f"## {title}")
        lines.append("")
        if not subset:
            lines.append("None.")
            lines.append("")
            return
        lines.append("| declaration | file | lines | file owner tags | file bridge tags | role |")
        lines.append("| --- | --- | --- | ---: | ---: | --- |")
        for r in subset:
            lines.append(
                f"| `{r['fqname']}` | `{r['file']}` | `{r['start_line']}-{r['end_line']}` | "
                f"{r['file_owner_count']} | {r['file_bridge_count']} | `{r['status']}` |"
            )
        lines.append("")

    add_table("Ownerless sockets", [r for r in rows if r["status"] == "ownerless_socket"])
    add_table("Bridge-backed sockets", [r for r in rows if r["status"] == "bridge_backed_socket"])
    lines.append("## Root-first ownerless sockets")
    lines.append("")
    ranked = ranked_ownerless_rows(rows)
    if not ranked:
        lines.append("None.")
        lines.append("")
    else:
        lines.append("| declaration | file | reverse deps | direct deps | owner tags in file | bridge tags in file |")
        lines.append("| --- | --- | ---: | ---: | ---: | ---: |")
        for r in ranked:
            lines.append(
                f"| `{r['fqname']}` | `{r['file']}` | {len(r.get('reverse_dependencies') or [])} | "
                f"{len(r.get('direct_dependencies') or [])} | {r['file_owner_count']} | {r['file_bridge_count']} |"
            )
        lines.append("")

    lines.append("## Fan-out-ranked ownerless sockets")
    lines.append("")
    impact_ranked = impact_ranked_ownerless_rows(rows)
    if not impact_ranked:
        lines.append("None.")
        lines.append("")
    else:
        lines.append("| declaration | file | reverse deps | direct deps | owner tags in file | bridge tags in file |")
        lines.append("| --- | --- | ---: | ---: | ---: | ---: |")
        for r in impact_ranked:
            lines.append(
                f"| `{r['fqname']}` | `{r['file']}` | {len(r.get('reverse_dependencies') or [])} | "
                f"{len(r.get('direct_dependencies') or [])} | {r['file_owner_count']} | {r['file_bridge_count']} |"
            )
        lines.append("")

    lines.append("## Local proof candidates for ownerless sockets")
    lines.append("")
    candidates = local_proof_candidates(graph, rows)
    if not candidates:
        lines.append("None.")
        lines.append("")
    else:
        for socket_name, cands in candidates.items():
            lines.append(f"### `{socket_name}`")
            if not cands:
                lines.append("No local candidate proof surfaces found.")
                lines.append("")
                continue
            for cand in cands:
                lines.append(
                    f"- `{cand['fqname']}` [{cand['template_role']}] "
                    f"`{cand['file']}:{cand['start_line']}-{cand['end_line']}` "
                    f"score={cand['score']} owner={cand['is_owner']} bridge={cand['is_bridge']}"
                )
            lines.append("")
    lines.append("## Notes")
    lines.append("")
    lines.append(
        "This ledger is derived from the repo's explicit `@[socket_debt_tag]` declarations "
        "and local owner/bridge tag density. It is an audit map for proof-plugging, not proof authority."
    )
    out.write_text("\n".join(lines), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("root", nargs="?", default=Path("lean/InfoGeometry"), type=Path)
    ap.add_argument("--out-dir", default=Path("reports/socket_debt_ledger"), type=Path)
    ap.add_argument("--filter-prefix", default="", help="Restrict the ledger to this declaration prefix")
    ap.add_argument("--wl-rounds", type=int, default=4, help="WL rounds passed through to the overlay scanner")
    args = ap.parse_args(argv)

    root = args.root.resolve()
    out_dir = args.out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    graph = build_graph(root, wl_rounds=args.wl_rounds)
    graph["wl_rounds"] = args.wl_rounds
    if args.filter_prefix:
        graph = filter_graph_by_prefix(graph, args.filter_prefix)
        graph["wl_rounds"] = args.wl_rounds

    rows = socket_rows(graph)
    write_json(graph, rows, out_dir / "socket_debt_ledger.json")
    write_markdown(graph, rows, out_dir / "socket_debt_ledger.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
