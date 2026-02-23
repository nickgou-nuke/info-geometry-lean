#!/usr/bin/env python3
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("InfoGeometry")

NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)\s*$")
DECL_RE = re.compile(r"^\s*(def|lemma|theorem|structure|class|inductive|abbrev|opaque|instance)\b")

SKIP_FILES = {
    "InfoGeometry/BlueprintTags.lean",
    "InfoGeometry/auto_blueprints.lean",
}

def suggested_namespace(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")  # e.g. Projective/FaithfulKL
    parts = ["InfoGeometry"] + list(rel.parts)
    # Drop common aggregator suffixes if present
    if parts[-1] in {"All", "Library", "Experimental"}:
        parts = parts[:-1]
    return ".".join(parts)

def main() -> int:
    rows = []
    for f in sorted(ROOT.rglob("*.lean")):
        s = str(f)
        if s in SKIP_FILES:
            continue

        text = f.read_text(encoding="utf-8", errors="ignore")
        lines = text.splitlines()

        first_ns = None
        for i, line in enumerate(lines, 1):
            m = NS_RE.match(line)
            if m:
                first_ns = (i, m.group(1))
                break

        has_decls = any(DECL_RE.match(line) for line in lines)

        if first_ns and first_ns[1].startswith("InfoGeometry"):
            status = "OK"
        elif not has_decls:
            status = "AGGREGATOR/NO-DECLS"
        elif first_ns:
            status = "NON-PROJECT-NS"
        else:
            status = "NO-NS"

        rows.append((status, s, first_ns[1] if first_ns else "", suggested_namespace(f)))

    # Print actionable rows first
    for status in ["NON-PROJECT-NS", "NO-NS", "AGGREGATOR/NO-DECLS", "OK"]:
        print(f"\n## {status}")
        for st, path, ns, sug in rows:
            if st != status:
                continue
            if ns:
                print(f"{path}\n  current:   {ns}\n  suggested: {sug}\n")
            else:
                print(f"{path}\n  current:   <none>\n  suggested: {sug}\n")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
