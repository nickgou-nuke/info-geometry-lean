from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from igf.artifacts.manifest import build_manifest, write_manifest
from igf.artifacts.compatibility_adapters import normalize_artifacts


GENERATOR = "tools/infra/build_chiral_patch_hashes.py"
GENERATOR_VERSION = "chiral_patch_hashes.v1.2"
DOCUMENTED_NODES = Path("artifacts/dag/index/decls.jsonl")
DOCUMENTED_EDGES = Path("artifacts/dag/index/edges.jsonl")
LEGACY_NODES = Path("artifacts/leantrail/arango/ig_nodes.jsonl")
LEGACY_EDGES = Path("artifacts/leantrail/arango/ig_edges.jsonl")


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _parse_summary(stdout: str) -> dict[str, Any]:
    text = stdout.strip()
    if not text:
        return {}
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        return {"raw_stdout": text}
    if isinstance(obj, dict):
        return obj
    return {"raw_stdout": text}


def resolve_graph_inputs(nodes: Path, edges: Path) -> tuple[Path, Path, bool]:
    compatibility_path_used = False
    resolved_nodes = nodes
    resolved_edges = edges

    if nodes == DOCUMENTED_NODES and not nodes.exists() and LEGACY_NODES.exists():
        resolved_nodes = LEGACY_NODES
        compatibility_path_used = True
    if edges == DOCUMENTED_EDGES and not edges.exists() and LEGACY_EDGES.exists():
        resolved_edges = LEGACY_EDGES
        compatibility_path_used = True

    return resolved_nodes, resolved_edges, compatibility_path_used


def build_chiral_patches(
    *,
    nodes: Path,
    edges: Path,
    fingerprints: Path | None,
    output_dir: Path,
    run_id: str | None = None,
    ego_limit: int = 40,
    ego_radius: int = 2,
    min_scc_size: int = 2,
    binder_min_size: int = 3,
    max_patch_nodes: int = 128,
    spectral_k: int = 8,
) -> dict[str, Any]:
    root = _repo_root()
    generator_path = root / GENERATOR
    nodes, edges, compatibility_path_used = resolve_graph_inputs(nodes, edges)
    cmd = [
        sys.executable,
        str(generator_path),
        "--nodes",
        str(nodes),
        "--edges",
        str(edges),
        "--output-dir",
        str(output_dir),
        "--ego-limit",
        str(ego_limit),
        "--ego-radius",
        str(ego_radius),
        "--min-scc-size",
        str(min_scc_size),
        "--binder-min-size",
        str(binder_min_size),
        "--max-patch-nodes",
        str(max_patch_nodes),
        "--spectral-k",
        str(spectral_k),
        "--print-json",
    ]
    if fingerprints is not None:
        cmd.extend(["--fingerprints", str(fingerprints)])
    if run_id:
        cmd.extend(["--run-id", run_id])

    completed = subprocess.run(
        cmd,
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )
    summary = _parse_summary(completed.stdout)
    if completed.returncode != 0:
        return {
            "ok": False,
            "command": cmd,
            "returncode": completed.returncode,
            "stdout": completed.stdout,
            "stderr": completed.stderr,
        }

    normalize_result = normalize_artifacts(output_dir, output_dir)
    resolved_run_id = str(summary.get("run_id") or summary.get("patch_run_id") or run_id or "")
    manifest = build_manifest(
        run_id=resolved_run_id,
        output_dir=output_dir,
        nodes=nodes,
        edges=edges,
        fingerprints=fingerprints,
        generator=GENERATOR,
        generator_version=GENERATOR_VERSION,
        build_summary=summary,
    )
    manifest_path = write_manifest(output_dir, manifest)
    return {
        "ok": True,
        "run_id": resolved_run_id,
        "summary": summary,
        "normalize": normalize_result,
        "manifest": str(manifest_path),
        "row_counts": manifest["row_counts"],
        "output_hashes": manifest["output_hashes"],
        "compatibility_path_used": compatibility_path_used,
    }
