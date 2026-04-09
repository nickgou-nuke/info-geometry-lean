#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import re
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from urllib.parse import unquote, urlparse

if __package__ in (None, ""):
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.pathing import normalize_user_path, repo_root


@dataclass(frozen=True)
class Edge:
    src: str
    dst: str
    kind: str
    detail: str | None = None


@dataclass(frozen=True)
class AuditFinding:
    file: str
    line: int | None
    name: str
    category: str
    priority: str


THINNESS_BONUS = {"high": 0.08, "medium": 0.04, "low": 0.015}
VACUITY_BONUS = {"high": 0.10, "medium": 0.05, "low": 0.02}
SURROGATE_BONUS = {"high": 0.12, "medium": 0.06, "low": 0.03}
UNIFICATION_ADJUSTMENT = {
    "repo_specific_unification": 0.03,
    "classical_adjacent_model": 0.015,
    "classical_specialization": 0.0,
    "mostly_classical": 0.0,
    "mixed_capstone_surface": -0.015,
    "packaging_heavy_bridge_surface": -0.03,
}
QUEUE_RE = re.compile(
    r"^- `(?P<priority>[^`]+)` `(?P<category>[^`]+)` `(?P<name>[^`]+)` at "
    r"`(?P<file>[^`:]+)(?::(?P<line>\d+))?`$"
)


def semantic_json_paths(inputs: list[str]) -> list[Path]:
    if inputs:
        return [normalize_user_path(x, repo_root() / x) for x in inputs]
    dag_dir = repo_root() / "reports" / "dag"
    return sorted(dag_dir.glob("*.semantic-block.stdlib.json"))


def load_payload(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def normalize_source_file(source_file: str) -> str:
    value = source_file.strip()
    if value.startswith("file://"):
        parsed = urlparse(value)
        value = unquote(parsed.path or value[len("file://") :])
    path = Path(value)
    if path.is_absolute():
        try:
            return str(path.resolve().relative_to(repo_root()))
        except ValueError:
            return str(path)
    return value


def parse_queue_audit(path: Path) -> list[AuditFinding]:
    if not path.exists():
        return []
    findings: list[AuditFinding] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        match = QUEUE_RE.match(line)
        if not match:
            continue
        findings.append(
            AuditFinding(
                file=match.group("file"),
                line=int(match.group("line")) if match.group("line") else None,
                name=match.group("name"),
                category=match.group("category"),
                priority=match.group("priority"),
            )
        )
    return findings


def parse_unification_statuses(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    statuses: dict[str, str] = {}
    in_table = False
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if line == "## Module Split":
            in_table = True
            continue
        if not in_table:
            continue
        if not line.startswith("|"):
            if statuses:
                break
            continue
        if line.startswith("| Module |") or line.startswith("| ---"):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if len(cells) < 2:
            continue
        module = cells[0].strip("`")
        status = cells[1].strip("`")
        if module and status:
            statuses[module] = status
    return statuses


def module_of_source_file(source_file: str) -> str:
    value = normalize_source_file(source_file)
    if value.startswith("lean/"):
        value = value[len("lean/") :]
    if value.endswith(".lean"):
        value = value[: -len(".lean")]
    return value.replace("/", ".")


def strongest_match(
    findings: list[AuditFinding], source_file: str, decls: list[str], stable_id: str
) -> AuditFinding | None:
    decl_set = set(decls)
    candidates = [
        finding
        for finding in findings
        if finding.file == source_file or finding.name in decl_set or finding.name == stable_id
    ]
    if not candidates:
        return None
    priority_order = {"high": 0, "medium": 1, "low": 2}
    return sorted(
        candidates,
        key=lambda finding: (
            priority_order.get(finding.priority, 9),
            finding.line if finding.line is not None else 10**9,
            finding.name,
        ),
    )[0]


def load_frontier_audits(root: Path) -> dict[str, Any]:
    return {
        "thinness": parse_queue_audit(root / "BRIDGE_THINNESS_INDEX.md"),
        "vacuity": parse_queue_audit(root / "VACUITY_INDEX.md"),
        "surrogate": parse_queue_audit(root / "SURROGATE_INDEX.md"),
        "unification": parse_unification_statuses(root / "UNIFICATION_INDEX.md"),
    }


def block_decl_names(block: dict[str, Any]) -> list[str]:
    xs = block.get("primaryProduces", [])
    return [str(x) for x in xs]


def block_primary_tag_map(block: dict[str, Any]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for entry in block.get("primarySpineTags", []):
        if isinstance(entry, dict):
            decl = str(entry.get("decl", ""))
            tags = [str(t) for t in entry.get("tags", [])]
            if decl:
                out[decl] = tags
        elif isinstance(entry, list) and len(entry) == 2:
            decl = str(entry[0])
            raw_tags = entry[1] if isinstance(entry[1], list) else []
            out[decl] = [str(t) for t in raw_tags]
    return out


class SemanticWeb:
    def __init__(self) -> None:
        self.nodes: dict[str, dict[str, Any]] = {}
        self.outgoing: dict[str, list[Edge]] = defaultdict(list)
        self.incoming: dict[str, list[Edge]] = defaultdict(list)
        self.produced_by: dict[str, str] = {}
        self.modules: dict[str, dict[str, Any]] = {}

    def add_module_payload(self, path: Path, payload: dict[str, Any]) -> None:
        source_file = str(payload.get("sourceFile", path.name))
        self.modules[source_file] = payload
        for block in payload.get("blocks", []):
            sid = str(block.get("stableId", ""))
            if not sid:
                continue
            self.nodes[sid] = {
                "stableId": sid,
                "sourceFile": source_file,
                "primaryProduces": block_decl_names(block),
                "primaryDeps": [str(x) for x in block.get("primaryDeps", [])],
                "primarySpineTags": block_primary_tag_map(block),
                "spineTags": [str(t) for t in block.get("spineTags", [])],
                "affects": [str(a) for a in block.get("affects", [])],
                "startPos": block.get("startPos", {}),
                "stopPos": block.get("stopPos", {}),
            }
            for decl in self.nodes[sid]["primaryProduces"]:
                self.produced_by[decl] = sid

        for edge in payload.get("edges", []):
            src = str(edge.get("srcStableId", ""))
            dst = str(edge.get("dstStableId", ""))
            kind = str(edge.get("kind", ""))
            if src and dst:
                self.add_edge(Edge(src=src, dst=dst, kind=kind))

    def add_edge(self, edge: Edge) -> None:
        self.outgoing[edge.src].append(edge)
        self.incoming[edge.dst].append(edge)

    def add_cross_module_affect_edges(self) -> int:
        added = 0
        seen: set[tuple[str, str, str, str | None]] = set()
        for sid, meta in self.nodes.items():
            dep_sources = [
                ("primaryDep", meta.get("primaryDeps", [])),
                ("affects", meta.get("affects", [])),
            ]
            for kind, deps in dep_sources:
                for dep in deps:
                    target = self.produced_by.get(dep)
                    if target is None or target == sid:
                        continue
                    key = (sid, target, kind, dep)
                    if key in seen:
                        continue
                    seen.add(key)
                    self.add_edge(Edge(src=sid, dst=target, kind=kind, detail=dep))
                    added += 1
        return added

    def seed_nodes(self, seeds: list[str]) -> list[str]:
        matches: list[str] = []
        for sid, meta in self.nodes.items():
            hay = [sid, meta.get("sourceFile", "")] + meta.get("primaryProduces", [])
            joined = "\n".join(hay)
            if any(seed in joined for seed in seeds):
                matches.append(sid)
        return sorted(set(matches))


def walk_neighbors(web: SemanticWeb, node: str, walk: str) -> list[Edge]:
    if walk == "forward":
        return list(web.outgoing.get(node, []))
    if walk == "reverse":
        return [Edge(src=node, dst=e.src, kind=e.kind, detail=e.detail) for e in web.incoming.get(node, [])]
    if walk == "both":
        seen: set[tuple[str, str, str, str | None]] = set()
        out: list[Edge] = []
        for e in web.outgoing.get(node, []):
            key = (e.src, e.dst, e.kind, e.detail)
            if key not in seen:
                seen.add(key)
                out.append(e)
        for e in web.incoming.get(node, []):
            rev = Edge(src=node, dst=e.src, kind=e.kind, detail=e.detail)
            key = (rev.src, rev.dst, rev.kind, rev.detail)
            if key not in seen:
                seen.add(key)
                out.append(rev)
        return out
    raise ValueError(f"unknown walk mode: {walk}")


def random_walk_with_restart(
    web: SemanticWeb,
    seeds: list[str],
    walk: str,
    restart: float = 0.2,
    steps: int = 50,
) -> dict[str, float]:
    if not seeds:
        return {}
    nodes = list(web.nodes.keys())
    seed_mass = 1.0 / len(seeds)
    p0 = {n: 0.0 for n in nodes}
    for s in seeds:
        p0[s] = seed_mass
    p = dict(p0)
    for _ in range(steps):
        nxt = {n: restart * p0[n] for n in nodes}
        dangling = 0.0
        for src in nodes:
            outs = walk_neighbors(web, src, walk)
            if not outs:
                dangling += (1.0 - restart) * p[src]
                continue
            share = (1.0 - restart) * p[src] / len(outs)
            for e in outs:
                nxt[e.dst] += share
        if dangling:
            spread = dangling / len(nodes)
            for n in nodes:
                nxt[n] += spread
        norm = sum(nxt.values())
        if norm > 0:
            for n in nodes:
                nxt[n] /= norm
        p = nxt
    return p


def frontier_candidates(
    web: SemanticWeb,
    ranks: dict[str, float],
    seeds: list[str],
    walk: str,
) -> list[dict[str, Any]]:
    seed_set = set(seeds)
    rows: list[dict[str, Any]] = []
    for sid, score in sorted(ranks.items(), key=lambda kv: kv[1], reverse=True):
        if sid in seed_set:
            continue
        meta = web.nodes[sid]
        seed_links: list[Edge] = []
        if walk in ("forward", "both"):
            seed_links.extend(e for e in web.incoming.get(sid, []) if e.src in seed_set)
        if walk in ("reverse", "both"):
            seed_links.extend(
                Edge(src=sid, dst=e.dst, kind=e.kind, detail=e.detail)
                for e in web.outgoing.get(sid, [])
                if e.dst in seed_set
            )
        rows.append(
            {
                "stableId": sid,
                "rawScore": score,
                "sourceFile": meta["sourceFile"],
                "repoSourceFile": normalize_source_file(meta["sourceFile"]),
                "primaryProduces": meta["primaryProduces"],
                "spineTags": meta["spineTags"],
                "affects": meta["affects"][:12],
                "seedLinkKinds": [e.kind for e in seed_links],
                "seedLinkDetails": [e.detail for e in seed_links if e.detail],
            }
        )
    return rows


def score_frontier_rows(rows: list[dict[str, Any]], audits: dict[str, Any]) -> list[dict[str, Any]]:
    scored: list[dict[str, Any]] = []
    for row in rows:
        source_file = str(row.get("repoSourceFile") or row["sourceFile"])
        decls = [str(x) for x in row.get("primaryProduces", [])]
        stable_id = str(row.get("stableId", ""))
        adjustments: list[dict[str, Any]] = []

        thin_match = strongest_match(audits.get("thinness", []), source_file, decls, stable_id)
        if thin_match is not None:
            value = THINNESS_BONUS.get(thin_match.priority, 0.0)
            adjustments.append(
                {
                    "kind": "thinness_debt_bonus",
                    "value": value,
                    "priority": thin_match.priority,
                    "category": thin_match.category,
                    "matchedName": thin_match.name,
                    "matchedFile": thin_match.file,
                }
            )

        vacuity_match = strongest_match(audits.get("vacuity", []), source_file, decls, stable_id)
        if vacuity_match is not None:
            value = VACUITY_BONUS.get(vacuity_match.priority, 0.0)
            adjustments.append(
                {
                    "kind": "vacuity_debt_bonus",
                    "value": value,
                    "priority": vacuity_match.priority,
                    "category": vacuity_match.category,
                    "matchedName": vacuity_match.name,
                    "matchedFile": vacuity_match.file,
                }
            )

        surrogate_match = strongest_match(audits.get("surrogate", []), source_file, decls, stable_id)
        if surrogate_match is not None:
            value = SURROGATE_BONUS.get(surrogate_match.priority, 0.0)
            adjustments.append(
                {
                    "kind": "surrogate_debt_bonus",
                    "value": value,
                    "priority": surrogate_match.priority,
                    "category": surrogate_match.category,
                    "matchedName": surrogate_match.name,
                    "matchedFile": surrogate_match.file,
                }
            )

        module_name = module_of_source_file(source_file)
        module_status = audits.get("unification", {}).get(module_name)
        if module_status is not None:
            value = UNIFICATION_ADJUSTMENT.get(module_status, 0.0)
            if not math.isclose(value, 0.0):
                adjustments.append(
                    {
                        "kind": "unification_status_adjustment",
                        "value": value,
                        "status": module_status,
                        "module": module_name,
                    }
                )

        adjusted_score = float(row["rawScore"]) + sum(float(item["value"]) for item in adjustments)
        scored.append(
            {
                **row,
                "score": adjusted_score,
                "scoreAdjustments": adjustments,
                "repoSourceFile": source_file,
                "moduleName": module_name,
                "moduleStatus": module_status,
            }
        )
    return scored


def unresolved_affects(web: SemanticWeb, seeds: list[str], limit: int) -> list[str]:
    unresolved: list[str] = []
    seen: set[str] = set()
    for sid in seeds:
        meta = web.nodes.get(sid, {})
        for dep in meta.get("affects", []):
            if dep in web.produced_by:
                continue
            if dep in seen:
                continue
            seen.add(dep)
            unresolved.append(dep)
            if len(unresolved) >= limit:
                return unresolved
    return unresolved


def render_markdown(
    web: SemanticWeb,
    seed_names: list[str],
    seeds: list[str],
    frontier: list[dict[str, Any]],
    walk: str,
    out_json: Path,
) -> str:
    lines: list[str] = []
    lines.append("# Skynet v2 Frontier Packet")
    lines.append("")
    lines.append("This is a report-only semantic frontier packet built from trusted semantic block JSON.")
    lines.append("")
    lines.append("## Seed")
    for s in seed_names:
        lines.append(f"- `{s}`")
    lines.append("")
    lines.append("## Seed Blocks")
    for sid in seeds:
        meta = web.nodes[sid]
        decls = ", ".join(meta["primaryProduces"]) or sid
        lines.append(f"- `{sid}` :: {decls}")
    lines.append("")
    lines.append("## Web Summary")
    edge_count = sum(len(v) for v in web.outgoing.values())
    lines.append(f"- nodes: `{len(web.nodes)}`")
    lines.append(f"- edges: `{edge_count}`")
    lines.append(f"- seed blocks: `{len(seeds)}`")
    lines.append(f"- walk mode: `{walk}`")
    lines.append(f"- modules loaded: `{len(web.modules)}`")
    lines.append("")
    lines.append("## Frontier")
    if not frontier:
        lines.append("- No frontier nodes ranked outside the seed set.")
    else:
        for row in frontier:
            decls = ", ".join(row["primaryProduces"]) or row["stableId"]
            tags = ", ".join(row["spineTags"]) or "-"
            seed_kinds = ", ".join(row["seedLinkKinds"]) or "-"
            score_bits = [f"priority-score: `{row['score']:.6f}`", f"raw-score: `{row['rawScore']:.6f}`"]
            if row.get("moduleStatus"):
                score_bits.append(f"module-status: `{row['moduleStatus']}`")
            lines.append(
                f"- `{decls}`\n"
                f"  source: `{row.get('repoSourceFile') or row['sourceFile']}`\n"
                f"  {' | '.join(score_bits)}\n"
                f"  tags: `{tags}`\n"
                f"  seed-links: `{seed_kinds}`"
            )
            for adjustment in row.get("scoreAdjustments", []):
                detail = adjustment.get("kind", "adjustment")
                value = float(adjustment.get("value", 0.0))
                extras: list[str] = []
                if adjustment.get("priority"):
                    extras.append(str(adjustment["priority"]))
                if adjustment.get("category"):
                    extras.append(str(adjustment["category"]))
                if adjustment.get("matchedName"):
                    extras.append(str(adjustment["matchedName"]))
                if adjustment.get("status"):
                    extras.append(str(adjustment["status"]))
                suffix = f" ({', '.join(extras)})" if extras else ""
                lines.append(f"  adjustment: `{detail}` `{value:+.3f}`{suffix}")
    lines.append("")
    unresolved = unresolved_affects(web, seeds, limit=15)
    lines.append("## Unresolved Seed Dependencies")
    if unresolved:
        for dep in unresolved:
            lines.append(f"- `{dep}`")
    else:
        lines.append("- none")
    lines.append("")
    lines.append(f"JSON packet: `{out_json}`")
    lines.append("")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description="Skynet v2: report-only semantic frontier explorer over trusted semantic block exports."
    )
    ap.add_argument(
        "--input",
        action="append",
        default=[],
        help="Semantic block JSON input. Defaults to all reports/dag/*.semantic-block.stdlib.json files.",
    )
    ap.add_argument(
        "--seed",
        action="append",
        default=[],
        help="Seed declaration/module substring. Repeatable.",
    )
    ap.add_argument(
        "--top",
        type=int,
        default=12,
        help="Number of frontier nodes to report.",
    )
    ap.add_argument(
        "--restart",
        type=float,
        default=0.2,
        help="Restart probability for random walk with restart.",
    )
    ap.add_argument(
        "--steps",
        type=int,
        default=50,
        help="Diffusion iterations.",
    )
    ap.add_argument(
        "--walk",
        choices=["forward", "reverse", "both"],
        default="both",
        help="Traversal direction over the semantic graph.",
    )
    ap.add_argument(
        "--json-out",
        default="reports/dag/skynet-v2-frontier.json",
        help="JSON output path.",
    )
    ap.add_argument(
        "--md-out",
        default="reports/dag/skynet-v2-frontier.md",
        help="Markdown output path.",
    )
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    inputs = semantic_json_paths(args.input)
    if not inputs:
        raise SystemExit("no semantic block JSON inputs found")
    seed_names = args.seed or ["KasparovCycle.analyticalIndex"]

    web = SemanticWeb()
    loaded: list[str] = []
    for path in inputs:
        try:
            payload = load_payload(path)
        except Exception:
            continue
        web.add_module_payload(path, payload)
        loaded.append(str(path))
    cross_module_edges = web.add_cross_module_affect_edges()
    seeds = web.seed_nodes(seed_names)
    if not seeds:
        raise SystemExit(f"no seed blocks matched {seed_names}")

    ranks = random_walk_with_restart(web, seeds, walk=args.walk, restart=args.restart, steps=args.steps)
    audits = load_frontier_audits(root)
    frontier = score_frontier_rows(frontier_candidates(web, ranks, seeds, walk=args.walk), audits)
    frontier.sort(key=lambda row: (row["score"], row["rawScore"]), reverse=True)
    frontier = frontier[: args.top]

    out_json = normalize_user_path(args.json_out, root / args.json_out)
    out_md = normalize_user_path(args.md_out, root / args.md_out)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_md.parent.mkdir(parents=True, exist_ok=True)

    payload = {
        "seedNames": seed_names,
        "seedBlocks": seeds,
        "seedStableIds": seeds,
        "walk": args.walk,
        "moduleCount": len(web.modules),
        "nodeCount": len(web.nodes),
        "edgeCount": sum(len(v) for v in web.outgoing.values()),
        "crossModuleEdgesAdded": cross_module_edges,
        "affectEdgesAdded": cross_module_edges,
        "loadedInputs": loaded,
        "frontier": frontier,
        "auditSignals": {
            "thinnessCount": len(audits.get("thinness", [])),
            "vacuityCount": len(audits.get("vacuity", [])),
            "surrogateCount": len(audits.get("surrogate", [])),
            "unificationModuleCount": len(audits.get("unification", {})),
        },
        "unresolvedSeedDependencies": unresolved_affects(web, seeds, limit=50),
    }
    out_json.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    out_md.write_text(render_markdown(web, seed_names, seeds, frontier, args.walk, out_json), encoding="utf-8")

    print(f"[skynet-v2] loaded inputs: {len(loaded)}")
    print(f"[skynet-v2] nodes: {len(web.nodes)}")
    print(f"[skynet-v2] edges: {sum(len(v) for v in web.outgoing.values())}")
    print(f"[skynet-v2] walk mode: {args.walk}")
    print(f"[skynet-v2] cross-module edges: {cross_module_edges}")
    print(f"[skynet-v2] seed blocks: {len(seeds)}")
    print(f"[skynet-v2] wrote {out_json}")
    print(f"[skynet-v2] wrote {out_md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
