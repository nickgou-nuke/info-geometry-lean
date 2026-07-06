#!/usr/bin/env python3
"""Read-only Lean owner source audit for the Hestenes/Krein complex axis packet.

This intentionally does not run lake, alter manifests, touch caches, or define a duplicate Lean theorem.
It verifies that the repository already owns the Lean statements mirrored by the CAS/prover packet.
"""
from __future__ import annotations
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
ROOT = Path(__file__).resolve().parent
packet = json.loads((ROOT / "cases.json").read_text())

def main() -> None:
    missing: list[str] = []
    for entry in packet["lean_owner_declarations"]:
        path = REPO / entry["file"]
        if not path.exists():
            missing.append(f"missing file {entry['file']}")
            continue
        text = path.read_text(errors="replace")
        for decl in entry["decls"]:
            # Permit namespace-qualified declarations by checking the terminal declaration token.
            token = decl.split(".")[-1]
            if token not in text:
                missing.append(f"{entry['file']} lacks token {decl}")
    if missing:
        raise SystemExit("LEAN_OWNER_AUDIT_FAILED\n" + "\n".join(missing))
    print("LEAN_OWNER_SOURCE_AUDIT_OK")

if __name__ == "__main__":
    main()
