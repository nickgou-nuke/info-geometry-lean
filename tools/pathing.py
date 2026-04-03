#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path


def repo_root() -> Path:
    # tools/ is expected to live at <repo>/tools/
    # this function returns the workspace root by walking up from this file.
    return Path(__file__).resolve().parents[1]


def lean_root() -> Path:
    r = repo_root()
    # support both layouts:
    # 1) repo/lean/InfoGeometry
    # 2) repo/InfoGeometry
    if (r / "lean" / "InfoGeometry").exists():
        return r / "lean"
    if (r / "InfoGeometry").exists():
        return r
    # fallback to repo root
    return r


def resolve_existing(*candidates: Path) -> Path:
    for p in candidates:
        if p.exists():
            return p
    return candidates[0]


def default_src_root() -> Path:
    l = lean_root()
    return l / "InfoGeometry"


def default_docs_map_root() -> Path:
    r = repo_root()
    return r / "docs-map"


def default_artifacts_root() -> Path:
    return repo_root() / "artifacts"


def default_decl_artifact_root() -> Path:
    return default_artifacts_root() / "dag"


def default_decl_graph_file() -> Path:
    return default_decl_artifact_root() / "full_graph.json"


def default_decl_index_dir() -> Path:
    return default_decl_artifact_root() / "index"


def default_decl_meta_file() -> Path:
    return default_decl_index_dir() / "meta.json"


def default_decl_metadata_file() -> Path:
    return default_decl_index_dir() / "decls.jsonl"


def default_source_sink_bipartite_file() -> Path:
    return default_decl_artifact_root() / "source-sink-bipartite.json"


def default_decl_structure_file() -> Path:
    return default_decl_artifact_root() / "structural-topology.json"


def default_build_decl_artifact_root() -> Path:
    return repo_root() / ".build"


def default_build_decl_graph_file() -> Path:
    return default_build_decl_artifact_root() / "full_graph.json"


def default_build_decl_index_dir() -> Path:
    return default_build_decl_artifact_root() / "index"


def default_build_decl_metadata_file() -> Path:
    return default_build_decl_index_dir() / "decls.jsonl"


def resolve_decl_graph_file() -> Path:
    return resolve_existing(default_decl_graph_file(), default_build_decl_graph_file())


def resolve_decl_metadata_file() -> Path:
    return resolve_existing(default_decl_metadata_file(), default_build_decl_metadata_file())


def default_auto_blueprints_file() -> Path:
    return default_src_root() / "auto_blueprints.lean"


def default_blueprint_tags_file() -> Path:
    return default_src_root() / "BlueprintTags.lean"


def default_blueprint_root() -> Path:
    return repo_root() / "blueprint"


def default_blueprint_generated_dir() -> Path:
    return default_blueprint_root() / "src" / "generated"


def normalize_user_path(p: str | None, default_path: Path) -> Path:
    if not p:
        return default_path
    q = Path(p)
    if q.is_absolute():
        return q
    # resolve relative to current working dir first (user intent), then repo root fallback
    cwd_q = (Path.cwd() / q).resolve()
    if cwd_q.exists():
        return cwd_q
    repo_q = (repo_root() / q).resolve()
    if repo_q.exists():
        return repo_q
    # if it doesn't exist yet (e.g. output file), prefer under cwd if parent exists, else repo
    if cwd_q.parent.exists():
        return cwd_q
    return repo_q
