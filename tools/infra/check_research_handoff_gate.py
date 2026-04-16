#!/usr/bin/env python3
"""ClawCode handoff gate for research-packet + NemoClaw provenance note."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

from tools.infra.research_packet import cmd_validate as _validate_cmd


REQUIRED_PROVENANCE_MARKERS = [
    "research provenance",
    "facts",
    "interpretations",
    "metaphors",
    "formalization candidates",
]


def check_nemoclaw_note(path: Path) -> list[str]:
    errs: list[str] = []
    if not path.exists():
        return [f"NemoClaw note missing: {path}"]
    text = path.read_text(encoding="utf-8", errors="ignore").lower()
    for marker in REQUIRED_PROVENANCE_MARKERS:
        if marker not in text:
            errs.append(f"NemoClaw note missing provenance marker: '{marker}'")
    return errs


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--packet", required=True, help="Path to research packet JSON.")
    p.add_argument("--nemoclaw-note", required=True, help="Path to NemoClaw architecture note (md/txt/json).")
    return p.parse_args()


def main() -> None:
    args = parse_args()

    class _Obj:
        packet = args.packet

    packet_rc = _validate_cmd(_Obj())
    errs = []
    if packet_rc != 0:
        errs.append("research packet validation failed")

    errs.extend(check_nemoclaw_note(Path(args.nemoclaw_note)))

    if errs:
        print("FAIL: research handoff gate")
        for e in errs:
            print(f"- {e}")
        raise SystemExit(1)
    print("PASS: research handoff gate")
    raise SystemExit(0)


if __name__ == "__main__":
    main()
