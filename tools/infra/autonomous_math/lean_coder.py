#!/usr/bin/env python3
"""Lean coder stage.

Writes a draft scaffold under reports/research/generated_lean.
It does not auto-import into canonical modules.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any


HEADER = """-- Auto-generated draft scaffold.
-- Source: autonomous_math pipeline
-- This file is intentionally not wired into build imports.

namespace InfoGeometry.AutonomousDraft

"""


def write_scaffold(formal_packet: dict[str, Any], out_dir: Path) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    file_path = out_dir / "autonomous_draft.lean"

    lines = [HEADER]
    lines.append("section Targets\n")
    targets = formal_packet.get("targets", [])
    if not isinstance(targets, list):
        targets = []
    for t in targets:
        if not isinstance(t, dict):
            continue
        kind = str(t.get("kind", "theorem")).strip()
        name = str(t.get("name", "unnamed_target")).strip() or "unnamed_target"
        hint = str(t.get("statement_hint", "")).strip()
        lines.append(f"-- hint: {hint}\n")
        if kind == "definition":
            lines.append(f"def {name} : Prop := True\n\n")
        else:
            lines.append(f"theorem {name} : True := by\n  trivial\n\n")
    lines.append("end Targets\n\nend InfoGeometry.AutonomousDraft\n")

    file_path.write_text("".join(lines), encoding="utf-8")
    return file_path

