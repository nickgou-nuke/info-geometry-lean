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
from pathlib import Path
from collections import Counter

from scripts.utils import prefix_match

from tools.pathing import default_docs_map_root, default_blueprint_tags_file, normalize_user_path


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
    lines.append("/-!")
    lines.append("AUTO-GENERATED FILE. DO NOT EDIT BY HAND.")
    lines.append("")
    lines.append("Generated by scripts/auto_tag.py to bulk-tag declarations with `[blueprint]`.")
    lines.append("This file is for coverage tagging only.")
    lines.append('Keep curated milestone labels as explicit `@[blueprint \"...\"]` in source files.')
    lines.append("-/")
    lines.append("")

    for imp in imports:
        lines.append(f"import {imp}")
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

    target = Path(args.target)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(output, encoding="utf-8")
    print(f"[auto_tag] wrote {target} ({len(selected)} attributes, {len(imports)} imports)")
    print(f"[auto_tag] stats: {dict(stats)}")


if __name__ == "__main__":
    main()