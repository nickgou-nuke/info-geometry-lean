#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
from pathlib import Path
from typing import Any

from tools.pathing import default_docs_map_root, default_src_root, normalize_user_path
from scripts.utils import load_json, dump_json, prefix_match


NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)\s*$")




def collect_declared_namespaces(src_root: Path) -> set[str]:
    out: set[str] = set()
    for f in sorted(src_root.rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        try:
            text = f.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for line in text.splitlines():
            m = NS_RE.match(line)
            if m:
                out.add(m.group(1))
                break  # first namespace line per file is enough for filtering
    return out


def prefix_match(name: str, prefix: str) -> bool:
    return name == prefix or name.startswith(prefix + ".")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", default=None,
                    help="Input declarations JSON")
    ap.add_argument("--src-root", default=None,
                    help="Root of lean sources (InfoGeometry) for namespace scanning")
    ap.add_argument("--out", default=None,
                    help="Output filtered JSON")
    ap.add_argument("--extra-prefix", action="append", default=[],
                    help="Additional declaration prefix to include (repeatable)")
    ap.add_argument("--exclude-prefix", action="append", default=[],
                    help="Declaration prefix to exclude (repeatable)")
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    src_root_default = default_src_root()

    inp_path = normalize_user_path(args.inp, docs_root / "declarations.debug.json")
    src_root = normalize_user_path(args.src_root, src_root_default)
    out_path = normalize_user_path(args.out, docs_root / "declarations.project.json")

    payload = load_json(inp_path)
    decls = payload["declarations"] if isinstance(payload, dict) and "declarations" in payload else payload

    declared_ns = collect_declared_namespaces(Path(args.src_root))
    declared_ns |= set(args.extra_prefix)

    # top-level prefixes from local source namespaces (e.g. PositiveMeasure, JaynesMaxEnt, InfoGeometry)
    include_prefixes = sorted(declared_ns)

    def included(name: str) -> bool:
        if not any(prefix_match(name, p) for p in include_prefixes):
            return False
        if any(prefix_match(name, p) for p in args.exclude_prefix):
            return False
        return True

    kept = [d for d in decls if isinstance(d, dict) and "name" in d and included(str(d["name"]))]

    out_payload = {
        "importModule": payload.get("importModule", ""),
        "namespace": "*",
        "depsPrefix": payload.get("depsPrefix", ""),
        "count": len(kept),
        "declarations": kept,
        "filter": {
            "sourceRoot": args.src_root,
            "includePrefixes": include_prefixes,
            "excludePrefixes": args.exclude_prefix,
        },
    }

    dump_json(out_path, out_payload)

    print(f"[filter_project_decls] source namespaces: {len(include_prefixes)}")
    print(f"[filter_project_decls] kept declarations: {len(kept)}")
    print(f"[filter_project_decls] wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
