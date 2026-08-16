#!/usr/bin/env python3
from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any

from tools.pathing import lean_root, repo_root

DEFAULT_DEPTH_INDEX = "reports/dag/representation-depth-index.json"
DEFAULT_LEAN_TAGS = "artifacts/dag/representation-depth-tags.json"


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def rel_repo_path(path: str | Path, root: Path | None = None) -> str:
    root = root or repo_root()
    p = Path(path)
    try:
        return str(p.resolve().relative_to(root.resolve()))
    except Exception:
        try:
            return str((root / p).resolve().relative_to(root.resolve()))
        except Exception:
            return str(path)


def interval_label(info_or_src: dict[str, Any] | int, dst: int | None = None) -> str:
    if isinstance(info_or_src, dict):
        src = int(info_or_src["source_depth"])
        dst_val = int(info_or_src["target_depth"])
    else:
        src = int(info_or_src)
        assert dst is not None
        dst_val = int(dst)
    return f"{src}→{dst_val}"


def load_depth_index(path: Path) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    payload = load_json(path)
    files_by_rel: dict[str, dict[str, Any]] = {}
    for row in payload.get("files", []):
        if not isinstance(row, dict):
            continue
        rel = str(row.get("file", ""))
        if not rel:
            continue
        files_by_rel[rel] = {
            "file": rel,
            "kind": str(row.get("kind", "")),
            "source_depth": int(row.get("source_depth", 0)),
            "target_depth": int(row.get("target_depth", 0)),
            "notes": str(row.get("notes", "")),
        }
    return files_by_rel, payload


def module_to_rel_file(module: str, root: Path | None = None) -> str:
    root = root or repo_root()
    module_path = Path(*module.split('.')).with_suffix('.lean')
    candidates = [lean_root() / module_path, root / module_path]
    for candidate in candidates:
        if candidate.exists():
            return rel_repo_path(candidate, root)
    return rel_repo_path(candidates[0], root)


def inferred_file_kind(rows: list[dict[str, Any]]) -> str:
    judgments = {str(row.get("judgment", "")) for row in rows if str(row.get("judgment", ""))}
    if not judgments:
        return "tagged"
    if "regression" in judgments or "wormhole" in judgments:
        return "violation"
    if judgments == {"vertical"}:
        return "owner"
    if judgments == {"primitive_translator"}:
        return "translator"
    if judgments <= {"vertical", "primitive_translator"} and "primitive_translator" in judgments:
        return "mixed"
    if "capstone_coherence" in judgments:
        return "coherence"
    return "mixed"


def load_lean_tags(path: Path, root: Path | None = None) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    root = root or repo_root()
    if not path.exists():
        return {}, {}
    payload = load_json(path)
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in payload.get("declarations", []):
        if not isinstance(row, dict):
            continue
        module = str(row.get("module", ""))
        if not module:
            continue
        try:
            depth_nat = int(row.get("depthNat", 0))
            source_depth_nat = int(row.get("sourceDepthNat", depth_nat))
            target_depth_nat = int(row.get("targetDepthNat", depth_nat))
        except Exception:
            continue
        rel = module_to_rel_file(module, root)
        grouped[rel].append(
            {
                "name": str(row.get("name", "")),
                "module": module,
                "kind": str(row.get("kind", "")),
                "depth": str(row.get("depth", "")),
                "depthNat": depth_nat,
                "sourceDepthNat": source_depth_nat,
                "targetDepthNat": target_depth_nat,
                "judgment": str(row.get("judgment", "")),
                "capstone": bool(row.get("capstone", False)),
            }
        )

    out: dict[str, dict[str, Any]] = {}
    for rel, rows in sorted(grouped.items()):
        source_depths = [int(row["sourceDepthNat"]) for row in rows]
        target_depths = [int(row["targetDepthNat"]) for row in rows]
        judgments = sorted({str(row.get("judgment", "")) for row in rows if str(row.get("judgment", ""))})
        out[rel] = {
            "file": rel,
            "kind": inferred_file_kind(rows),
            "source_depth": min(source_depths),
            "target_depth": max(target_depths),
            "tagged_decl_count": len(rows),
            "tagged_declarations": sorted(str(row["name"]) for row in rows if row.get("name")),
            "tagged_modules": sorted({str(row["module"]) for row in rows if row.get("module")}),
            "capstone_count": sum(1 for row in rows if bool(row.get("capstone", False))),
            "judgments": judgments,
        }
    return out, payload


def merge_depth_files(
    manual_files: dict[str, dict[str, Any]],
    lean_files: dict[str, dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    merged: dict[str, dict[str, Any]] = {}
    for rel in sorted(set(manual_files) | set(lean_files)):
        manual = manual_files.get(rel, {})
        lean = lean_files.get(rel, {})
        has_manual = bool(manual)
        has_lean = bool(lean)
        if has_manual and has_lean:
            source_depth = min(int(manual.get("source_depth", 0)), int(lean.get("source_depth", 0)))
            target_depth = max(int(manual.get("target_depth", manual.get("source_depth", 0))), int(lean.get("target_depth", 0)))
        elif has_lean:
            source_depth = int(lean.get("source_depth", 0))
            target_depth = int(lean.get("target_depth", source_depth))
        else:
            source_depth = int(manual.get("source_depth", 0))
            target_depth = int(manual.get("target_depth", source_depth))
        merged[rel] = {
            "file": rel,
            "kind": str(manual.get("kind", lean.get("kind", "tagged" if has_lean else "unknown"))),
            "source_depth": source_depth,
            "target_depth": target_depth,
            "notes": str(manual.get("notes", "")),
            "declared_by": (
                "lean+manual" if has_manual and has_lean else "lean" if has_lean else "manual"
            ),
            "tagged_decl_count": int(lean.get("tagged_decl_count", 0)),
            "tagged_declarations": list(lean.get("tagged_declarations", [])),
            "tagged_modules": list(lean.get("tagged_modules", [])),
            "capstone_count": int(lean.get("capstone_count", 0)),
            "judgments": list(lean.get("judgments", [])),
        }
    return merged


def build_depth_sources(
    depth_index_path: Path,
    lean_tags_path: Path,
    root: Path | None = None,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    root = root or repo_root()
    manual_files, manual_payload = load_depth_index(depth_index_path)
    lean_files, lean_payload = load_lean_tags(lean_tags_path, root)
    merged_files = merge_depth_files(manual_files, lean_files)
    payload = dict(manual_payload)
    payload["lean_tag_payload"] = lean_payload
    payload["source_meta"] = {
        "manual_index_path": rel_repo_path(depth_index_path, root),
        "manual_index_files": len(manual_files),
        "lean_tags_path": rel_repo_path(lean_tags_path, root),
        "lean_tagged_files": len(lean_files),
        "lean_tagged_declarations": int(lean_payload.get("count", 0)) if isinstance(lean_payload, dict) else 0,
        "merged_files": len(merged_files),
    }
    return merged_files, payload
