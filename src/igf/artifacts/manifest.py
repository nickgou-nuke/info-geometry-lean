from __future__ import annotations

from pathlib import Path
from typing import Any

from igf.artifacts.io import count_jsonl_rows, file_hashes, sha256_optional_file, write_json


ARTIFACT_FILES = [
    "ig_patch_runs.jsonl",
    "ig_chiral_patches.jsonl",
    "ig_patch_members.jsonl",
    "ig_patch_edges.jsonl",
    "ig_patch_spectral_signatures.jsonl",
]

SCHEMA_VERSIONS = {
    "ig_patch_runs.jsonl": "ig.patch_run.v1",
    "ig_chiral_patches.jsonl": "ig.chiral_patch.v1.2",
    "ig_patch_members.jsonl": "ig.patch_member.v1",
    "ig_patch_edges.jsonl": "ig.patch_edge.v1",
    "ig_patch_spectral_signatures.jsonl": "ig.patch_spectral_signature.v1.2",
}


def build_manifest(
    *,
    run_id: str,
    output_dir: Path,
    nodes: Path,
    edges: Path,
    fingerprints: Path | None,
    generator: str,
    generator_version: str,
    build_summary: dict[str, Any],
) -> dict[str, Any]:
    artifact_paths = [output_dir / name for name in ARTIFACT_FILES]
    manifest = {
        "run_id": run_id,
        "schema_versions": SCHEMA_VERSIONS,
        "generator": generator,
        "generator_version": generator_version,
        "inputs": {
            "nodes": str(nodes),
            "edges": str(edges),
            "fingerprints": str(fingerprints) if fingerprints else None,
        },
        "input_hashes": {
            "nodes": sha256_optional_file(nodes),
            "edges": sha256_optional_file(edges),
            "fingerprints": sha256_optional_file(fingerprints),
        },
        "outputs": {path.name: str(path) for path in artifact_paths},
        "output_hashes": file_hashes(artifact_paths),
        "row_counts": {path.name: count_jsonl_rows(path) for path in artifact_paths},
        "build_summary": build_summary,
    }
    return manifest


def write_manifest(output_dir: Path, manifest: dict[str, Any]) -> Path:
    path = output_dir / "manifest.json"
    write_json(path, manifest)
    return path
