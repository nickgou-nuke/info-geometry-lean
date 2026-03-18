#!/usr/bin/env python3
"""Generate Lean file containing bulk `attribute [blueprint]` annotations
for declarations listed in docs-map/declarations.json.

Coverage tagging only. Keep curated milestone labels as explicit
`@[blueprint "label"]` in source files.

Supports filtering by:
- declaration name prefix (`--ns`)
- defining module prefix (`--module-prefix`)
"""

import argparse
import json
import re
from pathlib import Path
from collections import Counter
import sys

if __package__ is None or __package__ == "":
    # Support direct execution: `python3 scripts/docs/auto_tag.py ...`
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.utils import prefix_match

from tools.pathing import default_docs_map_root, default_blueprint_tags_file, normalize_user_path

_DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|axiom|inductive|structure|class)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
_END_RE = re.compile(r"^\s*end\b")
_ATTR_RE = re.compile(r"^\s*attribute\s+\[blueprint(?:\s+\"[^\"]*\")?\]\s+(?P<rest>.+)$")


def load_declarations(path: Path):
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, dict) and "declarations" in data:
        raw = data["declarations"]
    elif isinstance(data, list):
        raw = data
    else:
        raise ValueError("unexpected declarations.json format")

    out = []
    for d in raw:
        if isinstance(d, dict):
            if "name" not in d:
                continue
            out.append({
                "name": str(d["name"]),
                "kind": str(d.get("kind", "")),
                "module": str(d.get("module", "")),
            })
        elif isinstance(d, list) and d:
            out.append({"name": str(d[0]), "kind": "", "module": ""})
        elif isinstance(d, str):
            out.append({"name": d, "kind": "", "module": ""})
    return out


def is_generated_or_unstable_name(name: str) -> bool:
    if name.startswith("_private.") or "._private." in name:
        return True
    patterns = [
        r"\.match(_\d+)?$",
        r"\.proof_\d+$",
        r"\._aux(_\d+)?$",
        r"\.brecOn$",
        r"\.below$",
        r"\.ibelow$",
        r"\.injEq$",
        r"\.sizeOf_spec$",
    ]
    return any(re.search(p, name) for p in patterns)


def module_to_path(module: str) -> Path | None:
    if not module or module == "<unknown>":
        return None
    return Path("lean") / Path(*module.split(".")).with_suffix(".lean")


def collect_explicit_blueprints(selected: list[dict[str, str]]) -> set[str]:
    by_name = {d["name"]: d for d in selected}
    explicit: set[str] = set()

    file_to_selected: dict[Path, list[dict[str, str]]] = {}
    for d in selected:
        path = module_to_path(d.get("module", ""))
        if path is None:
            continue
        file_to_selected.setdefault(path, []).append(d)

    for path, decls in file_to_selected.items():
        if not path.exists():
            continue
        if path.name in {"auto_blueprints.lean", "BlueprintTags.lean", "generated_blueprints.lean"}:
            continue

        visible_names = {d["name"] for d in decls}
        by_short: dict[str, list[str]] = {}
        for name in visible_names:
            by_short.setdefault(name.rsplit(".", 1)[-1], []).append(name)

        namespace_stack: list[str] = []
        pending_blueprint = False
        for raw in path.read_text(encoding="utf-8").splitlines():
            if m := _NAMESPACE_RE.match(raw):
                namespace_stack.append(m.group("name"))
                pending_blueprint = False
                continue
            if _END_RE.match(raw):
                if namespace_stack:
                    namespace_stack.pop()
                pending_blueprint = False
                continue
            if m := _ATTR_RE.match(raw):
                for tok in m.group("rest").split():
                    name = tok.strip(",")
                    if name in by_name:
                        explicit.add(name)
                pending_blueprint = False
                continue
            if "@[blueprint" in raw:
                pending_blueprint = True
                continue
            if pending_blueprint:
                stripped = raw.strip()
                if not stripped or stripped.startswith("--"):
                    continue
                m = _DECL_RE.match(raw)
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




def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--path", default=None,
                    help="Path to declarations JSON")
    ap.add_argument("--ns", default="", help="Declaration namespace prefix filter (by name)")
    ap.add_argument("--module-prefix", default="", help="Defining module prefix filter (e.g. InfoGeometry)")
    ap.add_argument("--target", default=None,
                    help="Lean file to generate and overwrite")
    ap.add_argument("--module", default="InfoGeometry.BlueprintTags",
                    help="Lean module name for generated file")
    ap.add_argument("--import-root", default="",
                    help="Optional root import (e.g. InfoGeometry.Library). If empty, imports defining modules.")
    ap.add_argument("--allow-kinds", default="theorem,def,axiom,opaque,inductive",
                    help="Comma-separated kinds to include")
    ap.add_argument("--skip-kinds", default="ctor,recursor,quot",
                    help="Comma-separated kinds to skip")
    ap.add_argument("--keep-generated", action="store_true",
                    help="Do not filter generated/internal names")
    ap.add_argument("--dry-run", action="store_true",
                    help="Print generated file instead of writing it")
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    decls_path = normalize_user_path(args.path, docs_root / "declarations.json")
    target_path = normalize_user_path(args.target, default_blueprint_tags_file())

    decls = load_declarations(decls_path)
    allow_kinds = {k.strip() for k in args.allow_kinds.split(",") if k.strip()}
    skip_kinds = {k.strip() for k in args.skip_kinds.split(",") if k.strip()}

    stats = Counter()
    selected = []

    for d in decls:
        nm = d["name"]
        kd = d.get("kind", "")
        mod = d.get("module", "")

        if args.ns and not prefix_match(nm, args.ns):
            stats["skip_ns"] += 1
            continue
        if args.module_prefix and not prefix_match(mod, args.module_prefix):
            stats["skip_module"] += 1
            continue
        if mod == args.module:
            stats["skip_self_module"] += 1
            continue
        if kd and kd in skip_kinds:
            stats["skip_kind"] += 1
            continue
        if kd and allow_kinds and kd not in allow_kinds:
            stats["skip_not_allowed_kind"] += 1
            continue
        if not args.keep_generated and is_generated_or_unstable_name(nm):
            stats["skip_generated"] += 1
            continue
        if any(c.isspace() for c in nm):
            stats["skip_whitespace_name"] += 1
            continue

        selected.append({"name": nm, "kind": kd, "module": mod})
        stats["selected_raw"] += 1

    # dedupe by name
    by_name = {d["name"]: d for d in selected}
    selected = [by_name[k] for k in sorted(by_name.keys())]
    stats["selected_unique"] = len(selected)

    explicit_blueprints = collect_explicit_blueprints(selected)
    if explicit_blueprints:
        selected = [d for d in selected if d["name"] not in explicit_blueprints]
        stats["skip_existing_blueprint"] = len(explicit_blueprints)
        stats["selected_after_existing_filter"] = len(selected)

    # imports
    imports = ["Architect"]
    if args.import_root:
        imports.append(args.import_root)
    else:
        mods = sorted({
            d["module"]
            for d in selected
            if d.get("module") and d["module"] not in {"<unknown>", args.module}
        })
        imports.extend(mods)

    lines = []
    for imp in imports:
        lines.append(f"import {imp}")
    lines.append("")
    lines.append("/-!")
    lines.append("AUTO-GENERATED FILE. DO NOT EDIT BY HAND.")
    lines.append("")
    lines.append("Generated by scripts/auto_tag.py to bulk-tag declarations with `[blueprint]`.")
    lines.append("This file is for coverage tagging only.")
    lines.append('Keep curated milestone labels as explicit `@[blueprint \"...\"]` in source files.')
    lines.append("-/")
    lines.append("")
    lines.append("-- auto-generated blueprint annotations")
    for d in selected:
        lines.append(f"attribute [blueprint] {d['name']}")

    output = "\n".join(lines) + "\n"

    if args.dry_run:
        print(output)
        print(f"-- [auto_tag] would generate {len(selected)} attributes ({len(imports)} imports)")
        print(f"-- [auto_tag] stats: {dict(stats)}")
        return

    target = target_path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(output, encoding="utf-8")
    print(f"[auto_tag] wrote {target} ({len(selected)} attributes, {len(imports)} imports)")
    print(f"[auto_tag] stats: {dict(stats)}")


if __name__ == "__main__":
    main()
