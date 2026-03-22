#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import (
        default_auto_blueprints_file,
        default_blueprint_tags_file,
        resolve_decl_metadata_file,
        repo_root,
    )
else:
    from tools.pathing import (
        default_auto_blueprints_file,
        default_blueprint_tags_file,
        resolve_decl_metadata_file,
        repo_root,
    )

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom|inductive|structure|class|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
END_RE = re.compile(r"^\s*end\b")
ATTR_RE = re.compile(r"^\s*attribute\s+\[blueprint(?:\s+\"[^\"]*\")?\]\s+(?P<rest>.+)$")

DEFAULT_ALLOW_KINDS = {"theorem", "def", "opaque", "axiom", "inductive"}
DEFAULT_SKIP_KINDS = {"constructor", "recursor", "quotient"}


def parse_args() -> argparse.Namespace:
    root = repo_root()
    parser = argparse.ArgumentParser(
        description=(
            "Refresh the authoritative LeanArchitect-facing blueprint coverage layer from the "
            "public declaration metadata export under artifacts/dag/."
        )
    )
    parser.add_argument(
        "--decls",
        default=str(resolve_decl_metadata_file().relative_to(root)),
        help="Path to the authoritative decls.jsonl export.",
    )
    parser.add_argument(
        "--target",
        default=str(default_auto_blueprints_file().relative_to(root)),
        help="Lean file that receives the bulk `attribute [blueprint]` coverage tags.",
    )
    parser.add_argument(
        "--facade",
        default=str(default_blueprint_tags_file().relative_to(root)),
        help="LeanArchitect-facing façade module to refresh alongside the bulk tag file.",
    )
    parser.add_argument(
        "--import-root",
        default="InfoGeometry.All",
        help="Lean import root for the generated bulk tag file.",
    )
    parser.add_argument("--ns", default="InfoGeometry", help="Declaration namespace prefix filter.")
    parser.add_argument(
        "--allow-kinds",
        default=",".join(sorted(DEFAULT_ALLOW_KINDS)),
        help="Comma-separated declaration kinds to include from decls.jsonl.",
    )
    parser.add_argument(
        "--skip-kinds",
        default=",".join(sorted(DEFAULT_SKIP_KINDS)),
        help="Comma-separated declaration kinds to skip from decls.jsonl.",
    )
    parser.add_argument(
        "--keep-generated",
        action="store_true",
        help="Do not filter generated/internal declaration names.",
    )
    return parser.parse_args()


def normalize_user_path(path: str, root: Path) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate.resolve()
    return (root / candidate).resolve()


def load_decl_rows(path: Path) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line:
            continue
        obj = json.loads(line)
        name = str(obj.get("name", "")).strip()
        if not name:
            continue
        out.append(
            {
                "name": name,
                "kind": str(obj.get("kind", "")).strip(),
                "module": str(obj.get("module", "")).strip(),
                "file": str(obj.get("file", "")).strip(),
            }
        )
    return out


def is_generated_or_unstable_name(name: str) -> bool:
    if name.startswith("_private.") or "._private." in name:
        return True
    patterns = [
        r"\._",
        r"\.match(_\d+)?$",
        r"\.proof_\d+$",
        r"\._aux(_\d+)?$",
        r"\.brecOn$",
        r"\.below$",
        r"\.ibelow$",
        r"\.injEq$",
        r"\.sizeOf_spec$",
        r"\.casesOn$",
        r"\.rec(On)?$",
        r"\.noConfusion(Type)?$",
        r"\.ctorIdx$",
    ]
    return any(re.search(pattern, name) for pattern in patterns)


def prefix_match(name: str, prefix: str) -> bool:
    if not prefix:
        return True
    return name == prefix or name.startswith(prefix + ".")


def module_to_path(module: str) -> Path | None:
    if not module or module == "<unknown>":
        return None
    return Path("lean") / Path(*module.split(".")).with_suffix(".lean")


def collect_explicit_blueprints(root: Path, selected: list[dict[str, str]]) -> set[str]:
    by_name = {row["name"]: row for row in selected}
    explicit: set[str] = set()

    file_to_selected: dict[Path, list[dict[str, str]]] = {}
    for row in selected:
        path = module_to_path(row.get("module", ""))
        if path is None:
            continue
        file_to_selected.setdefault(root / path, []).append(row)

    for path, rows in file_to_selected.items():
        if not path.exists():
            continue
        if path.name in {"auto_blueprints.lean", "BlueprintTags.lean", "generated_blueprints.lean"}:
            continue

        visible_names = {row["name"] for row in rows}
        by_short: dict[str, list[str]] = {}
        for name in visible_names:
            by_short.setdefault(name.rsplit(".", 1)[-1], []).append(name)

        namespace_stack: list[str] = []
        pending_blueprint = False
        for raw in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            stripped = raw.strip()
            if m := NAMESPACE_RE.match(stripped):
                namespace_stack.append(m.group("name"))
                pending_blueprint = False
                continue
            if END_RE.match(stripped):
                if namespace_stack:
                    namespace_stack.pop()
                pending_blueprint = False
                continue
            if m := ATTR_RE.match(stripped):
                for tok in m.group("rest").split():
                    candidate = tok.strip(",")
                    if candidate in by_name:
                        explicit.add(candidate)
                pending_blueprint = False
                continue
            if "@[blueprint" in stripped:
                pending_blueprint = True
                continue
            if pending_blueprint:
                if not stripped or stripped.startswith("--"):
                    continue
                m = DECL_RE.match(raw)
                if m:
                    short = m.group("name")
                    candidates: list[str] = []
                    if "." in short and short in by_name:
                        candidates = [short]
                    elif namespace_stack:
                        qualified = f"{namespace_stack[-1]}.{short}"
                        if qualified in by_name:
                            candidates = [qualified]
                    if not candidates:
                        candidates = by_short.get(short, [])
                    if len(candidates) == 1:
                        explicit.add(candidates[0])
                pending_blueprint = False

    return explicit


def render_auto_blueprints(import_root: str, selected: list[dict[str, str]], source_path: Path) -> str:
    lines: list[str] = [
        "import Architect",
        f"import {import_root}",
        "",
        "/-!",
        "AUTO-GENERATED FILE. DO NOT EDIT BY HAND.",
        "",
        f"Generated by `tools/refresh_blueprint_tags.py` from `{source_path}`.",
        "This file provides bulk `attribute [blueprint]` coverage tags for LeanArchitect.",
        'Keep curated milestone labels as explicit `@[blueprint \"...\"]` in source files.',
        "-/",
        "",
        "-- auto-generated blueprint annotations",
    ]
    for row in selected:
        lines.append(f"attribute [blueprint] {row['name']}")
    lines.append("")
    return "\n".join(lines)


def render_blueprint_facade(auto_module: str) -> str:
    lines = [
        "import Architect",
        f"import {auto_module}",
        "",
        "/-!",
        "# InfoGeometry.BlueprintTags",
        "",
        "LeanArchitect-facing blueprint surface.",
        "",
        "This module imports the generated bulk `[blueprint]` coverage layer without pulling it",
        "into the main `InfoGeometry.All` publication surface by default.",
        "",
        "Refresh path:",
        "- `python3 tools/refresh_decl_graph.py`",
        "- `python3 tools/refresh_blueprint_tags.py`",
        "- `lake build InfoGeometry.BlueprintTags:blueprint`",
        "- `lake build InfoGeometry.BlueprintTags:blueprintJson`",
        "-/",
        "",
        "namespace InfoGeometry.BlueprintTags",
        "",
        "-- declarations are registered in `InfoGeometry.auto_blueprints`",
        "-- and exposed through this dedicated LeanArchitect-facing module.",
        "",
        "end InfoGeometry.BlueprintTags",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    root = repo_root()
    decls_path = normalize_user_path(args.decls, root)
    target_path = normalize_user_path(args.target, root)
    facade_path = normalize_user_path(args.facade, root)

    rows = load_decl_rows(decls_path)
    allow_kinds = {item.strip() for item in args.allow_kinds.split(",") if item.strip()}
    skip_kinds = {item.strip() for item in args.skip_kinds.split(",") if item.strip()}

    stats = Counter()
    selected: list[dict[str, str]] = []
    for row in rows:
        name = row["name"]
        kind = row.get("kind", "")
        module = row.get("module", "")
        if args.ns and not prefix_match(name, args.ns):
            stats["skip_ns"] += 1
            continue
        if module == "InfoGeometry.BlueprintTags":
            stats["skip_facade_module"] += 1
            continue
        if kind and kind in skip_kinds:
            stats["skip_kind"] += 1
            continue
        if kind and allow_kinds and kind not in allow_kinds:
            stats["skip_not_allowed_kind"] += 1
            continue
        if not args.keep_generated and is_generated_or_unstable_name(name):
            stats["skip_generated"] += 1
            continue
        selected.append({"name": name, "kind": kind, "module": module})
        stats["selected_raw"] += 1

    selected_by_name = {row["name"]: row for row in selected}
    selected = [selected_by_name[name] for name in sorted(selected_by_name)]
    stats["selected_unique"] = len(selected)

    explicit = collect_explicit_blueprints(root, selected)
    if explicit:
        selected = [row for row in selected if row["name"] not in explicit]
        stats["skip_existing_blueprint"] = len(explicit)
    stats["selected_final"] = len(selected)

    target_path.parent.mkdir(parents=True, exist_ok=True)
    facade_path.parent.mkdir(parents=True, exist_ok=True)

    relative_decls = str(decls_path.relative_to(root)) if decls_path.is_relative_to(root) else str(decls_path)
    target_path.write_text(
        render_auto_blueprints(args.import_root, selected, Path(relative_decls)),
        encoding="utf-8",
    )
    facade_module = ".".join(facade_path.relative_to(root / "lean").with_suffix("").parts)
    auto_module = ".".join(target_path.relative_to(root / "lean").with_suffix("").parts)
    facade_path.write_text(render_blueprint_facade(auto_module), encoding="utf-8")

    print(f"[refresh-blueprint-tags] wrote {target_path}")
    print(f"[refresh-blueprint-tags] wrote {facade_path}")
    print(f"[refresh-blueprint-tags] stats: {dict(stats)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
