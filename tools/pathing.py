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
    l = lean_root()
    return l / "docs-map"


def default_blueprint_tags_file() -> Path:
    return default_src_root() / "BlueprintTags.lean"


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
