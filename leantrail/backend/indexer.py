from __future__ import annotations

import argparse
import json
import subprocess
from collections import defaultdict, deque
from pathlib import Path
from typing import Any, Iterable

from .extractor import run_refresh_pipeline
from .models import EdgeRecord, GraphSnapshot
from .normalizer import LeanTrailNormalizer


def _run_git_lines(repo_root: Path, args: list[str]) -> list[str]:
    try:
        out = subprocess.check_output(["git", *args], cwd=repo_root, text=True)
    except Exception:
        return []
    return [line.strip() for line in out.splitlines() if line.strip()]


def _safe_git_head(repo_root: Path) -> str:
    lines = _run_git_lines(repo_root, ["rev-parse", "HEAD"])
    if lines:
        return lines[0]
    return "unknown"


def _iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)


def _module_from_lean_path(path: Path) -> str | None:
    parts = path.parts
    if len(parts) < 2 or path.suffix != ".lean":
        return None
    stem_parts = path.with_suffix("").parts
    if stem_parts[0] == "lean":
        stem_parts = stem_parts[1:]
    elif stem_parts[0] != "InfoGeometry":
        return None
    if not stem_parts:
        return None
    return ".".join(stem_parts)


def _detect_changed_modules(repo_root: Path, since_commit: str | None) -> set[str]:
    changed_paths: set[str] = set()
    if since_commit and since_commit not in {"", "unknown"}:
        changed_paths.update(
            _run_git_lines(repo_root, ["diff", "--name-only", f"{since_commit}..HEAD"])
        )
    changed_paths.update(_run_git_lines(repo_root, ["diff", "--name-only", "HEAD"]))
    changed_paths.update(_run_git_lines(repo_root, ["ls-files", "--others", "--exclude-standard"]))

    modules: set[str] = set()
    for rel in changed_paths:
        module = _module_from_lean_path(Path(rel))
        if module:
            modules.add(module)
    return modules


def _collect_decl_to_module(repo_root: Path) -> dict[str, str]:
    decl_file = repo_root / "artifacts" / "dag" / "index" / "decls.jsonl"
    mapping: dict[str, str] = {}
    if not decl_file.exists():
        return mapping
    for row in _iter_jsonl(decl_file):
        name = str(row.get("name", "")).strip()
        module = str(row.get("module", "")).strip()
        if name and module:
            mapping[name] = module
    return mapping


def _compute_impacted_modules(
    repo_root: Path,
    seed_modules: set[str],
    radius: int,
    decl_to_module: dict[str, str] | None = None,
) -> set[str]:
    if not seed_modules:
        return set()
    if radius <= 0:
        return set(seed_modules)

    decl_to_mod = decl_to_module or _collect_decl_to_module(repo_root)
    edge_file = repo_root / "artifacts" / "dag" / "index" / "edges.jsonl"
    adjacency: dict[str, set[str]] = defaultdict(set)

    if edge_file.exists():
        for row in _iter_jsonl(edge_file):
            src = str(row.get("src", "")).strip()
            dst = str(row.get("dst", "")).strip()
            src_mod = decl_to_mod.get(src)
            dst_mod = decl_to_mod.get(dst)
            if not src_mod or not dst_mod or src_mod == dst_mod:
                continue
            adjacency[src_mod].add(dst_mod)
            adjacency[dst_mod].add(src_mod)

    visited = set(seed_modules)
    q: deque[tuple[str, int]] = deque((mod, 0) for mod in sorted(seed_modules))
    while q:
        mod, depth = q.popleft()
        if depth >= radius:
            continue
        for nxt in adjacency.get(mod, ()):
            if nxt in visited:
                continue
            visited.add(nxt)
            q.append((nxt, depth + 1))
    return visited


def _edge_key(edge: EdgeRecord) -> tuple[str, str, str, float, str]:
    return (edge.src, edge.dst, edge.kind, edge.weight, edge.evidence_ref)


def _merge_incremental_snapshot(
    base: GraphSnapshot,
    patch: GraphSnapshot,
    impacted_modules: set[str],
    *,
    changed_modules: set[str],
    since_commit: str,
    current_commit: str,
    radius: int,
) -> GraphSnapshot:
    impacted = set(impacted_modules)
    kept_base_nodes = [node for node in base.nodes if node.module not in impacted]
    node_by_id = {node.id: node for node in kept_base_nodes}
    for node in patch.nodes:
        node_by_id[node.id] = node
    merged_nodes = list(node_by_id.values())

    node_module = {node.id: node.module for node in merged_nodes}

    def touches_impacted(edge: EdgeRecord) -> bool:
        return node_module.get(edge.src) in impacted or node_module.get(edge.dst) in impacted

    kept_base_edges = [edge for edge in base.edges if not touches_impacted(edge)]
    edge_by_key = {_edge_key(edge): edge for edge in kept_base_edges}
    for edge in patch.edges:
        edge_by_key[_edge_key(edge)] = edge
    merged_edges = list(edge_by_key.values())

    metadata = dict(base.metadata)
    metadata.update(patch.metadata)
    metadata["incremental"] = {
        "enabled": True,
        "since_commit": since_commit,
        "current_commit": current_commit,
        "changed_modules": sorted(changed_modules),
        "impacted_modules": sorted(impacted_modules),
        "radius": radius,
    }
    metadata["counts"] = {
        "nodes": len(merged_nodes),
        "edges": len(merged_edges),
        "depth_rows": patch.metadata.get("counts", {}).get("depth_rows"),
    }
    return GraphSnapshot(metadata=metadata, nodes=merged_nodes, edges=merged_edges)


def build_snapshot(
    repo_root: Path,
    snapshot_out: Path,
    refresh: bool = False,
    max_process_events: int | None = None,
    incremental: bool = False,
    incremental_radius: int = 1,
) -> Path:
    repo_root = repo_root.resolve()
    if not snapshot_out.is_absolute():
        snapshot_out = (repo_root / snapshot_out).resolve()

    if refresh:
        run_refresh_pipeline(repo_root)

    normalizer = LeanTrailNormalizer(repo_root)
    current_commit = _safe_git_head(repo_root)
    snapshot: GraphSnapshot

    if incremental and snapshot_out.exists():
        try:
            base_payload = json.loads(snapshot_out.read_text(encoding="utf-8"))
            base_snapshot = GraphSnapshot.from_dict(base_payload)
            since_commit = str(base_snapshot.metadata.get("commit_sha", "")).strip()
            if not since_commit or since_commit == "unknown":
                raise ValueError("missing commit_sha in existing snapshot")

            changed_modules = _detect_changed_modules(repo_root, since_commit)
            if changed_modules:
                decl_to_mod = _collect_decl_to_module(repo_root)
                impacted = _compute_impacted_modules(
                    repo_root=repo_root,
                    seed_modules=changed_modules,
                    radius=incremental_radius,
                    decl_to_module=decl_to_mod,
                )
                patch_snapshot = normalizer.build_snapshot(
                    max_process_events=max_process_events,
                    include_modules=impacted,
                )
                snapshot = _merge_incremental_snapshot(
                    base_snapshot,
                    patch_snapshot,
                    impacted_modules=impacted,
                    changed_modules=changed_modules,
                    since_commit=since_commit,
                    current_commit=current_commit,
                    radius=incremental_radius,
                )
            else:
                metadata = dict(base_snapshot.metadata)
                metadata["incremental"] = {
                    "enabled": True,
                    "since_commit": since_commit,
                    "current_commit": current_commit,
                    "changed_modules": [],
                    "impacted_modules": [],
                    "radius": incremental_radius,
                    "reused_snapshot": True,
                }
                snapshot = GraphSnapshot(
                    metadata=metadata,
                    nodes=base_snapshot.nodes,
                    edges=base_snapshot.edges,
                )
        except Exception:
            snapshot = normalizer.build_snapshot(max_process_events=max_process_events)
            snapshot.metadata["incremental"] = {
                "enabled": False,
                "fallback_full_rebuild": True,
            }
    else:
        snapshot = normalizer.build_snapshot(max_process_events=max_process_events)
        if incremental:
            snapshot.metadata["incremental"] = {
                "enabled": False,
                "fallback_full_rebuild": True,
            }

    snapshot_out.parent.mkdir(parents=True, exist_ok=True)
    snapshot_out.write_text(
        json.dumps(snapshot.to_dict(), indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )
    return snapshot_out


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build LeanTrail normalized graph snapshot.")
    parser.add_argument(
        "--repo-root",
        default=".",
        help="Repository root.",
    )
    parser.add_argument(
        "--snapshot-out",
        default="artifacts/leantrail/graph_snapshot.json",
        help="Output snapshot JSON path.",
    )
    parser.add_argument(
        "--refresh",
        action="store_true",
        help="Run the locked extractor pipeline before normalization.",
    )
    parser.add_argument(
        "--max-process-events",
        type=int,
        default=None,
        help="Optional cap when ingesting process-flow events.",
    )
    parser.add_argument(
        "--incremental",
        action="store_true",
        help="Patch/prune only changed module neighborhoods over the previous snapshot.",
    )
    parser.add_argument(
        "--incremental-radius",
        type=int,
        default=1,
        help="Module-neighborhood BFS radius for incremental patching (default: 1).",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    repo_root = Path(args.repo_root)
    snapshot_out = Path(args.snapshot_out)
    out = build_snapshot(
        repo_root=repo_root,
        snapshot_out=snapshot_out,
        refresh=args.refresh,
        max_process_events=args.max_process_events,
        incremental=args.incremental,
        incremental_radius=args.incremental_radius,
    )
    print(f"LeanTrail snapshot written: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
