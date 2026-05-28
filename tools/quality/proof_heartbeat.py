#!/usr/bin/env python3
"""Lean proof heartbeat for the proof-only cleanup loop.

The heartbeat is intentionally diagnostic only: it does not decide that a
certificate/witness surface is mathematically valid.  It reports visible proof
holes and common vacuity/proxy patterns so the next cleanup iteration can pick a
small owner file and either prove it from lower lemmas or delete the proxy.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lean4-skills"))
try:
    from sorry_analyzer import find_sorries_in_file
except Exception:  # pragma: no cover - fallback for unusual invocation environments
    find_sorries_in_file = None

SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])\bsorry\b(?![A-Za-z0-9_'])")
FIELD_PROXY_RE = re.compile(
    r"^\s+(?P<name>[A-Za-z0-9_']*(?:_law|_valid|_readback|_certificate|_witness|_socket))\s*:",
    re.MULTILINE,
)
PROP_SOCKET_RE = re.compile(
    r"^\s+(?P<name>[A-Za-z0-9_']*(?:law|valid|readback|certificate|witness|socket)[A-Za-z0-9_']*)\s*:\s*Prop\b",
    re.MULTILINE,
)
DECL_RE = re.compile(r"^\s*(?:theorem|lemma)\s+(?P<name>[A-Za-z0-9_']+)\b")
PROXY_USE_RE = re.compile(r"\b[A-Za-z0-9_'.]+_(?:law|certificate|witness|readback|valid|socket)\b")


def lean_files(root: Path):
    for path in root.rglob("*.lean"):
        if any(part in {".lake", ".changes"} for part in path.parts):
            continue
        yield path


def line_of(text: str, idx: int) -> int:
    return text.count("\n", 0, idx) + 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", nargs="?", default="lean/InfoGeometry")
    parser.add_argument("--top", type=int, default=20)
    args = parser.parse_args()

    root = Path(args.root)
    counts: Counter[str] = Counter()
    examples: dict[str, list[str]] = defaultdict(list)

    for path in lean_files(root):
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        rel = str(path)

        if find_sorries_in_file is not None:
            sorries = find_sorries_in_file(path)
            counts["sorry"] += len(sorries)
            for sorry in sorries[:3]:
                examples["sorry"].append(f"{sorry.file}:{sorry.line}")
        else:
            sorries = list(SORRY_RE.finditer(text))
            if sorries:
                counts["sorry"] += len(sorries)
                for m in sorries[:3]:
                    examples["sorry"].append(f"{rel}:{line_of(text, m.start())}")

        for label, regex in [
            ("proxy_field", FIELD_PROXY_RE),
            ("prop_socket", PROP_SOCKET_RE),
        ]:
            matches = list(regex.finditer(text))
            if matches:
                counts[label] += len(matches)
                for m in matches[:3]:
                    name = m.groupdict().get("name", "?")
                    examples[label].append(f"{rel}:{line_of(text, m.start())}:{name}")

        lines = text.splitlines()
        for i, line in enumerate(lines):
            decl = DECL_RE.match(line)
            if not decl:
                continue
            window = "\n".join(lines[i : min(i + 12, len(lines))])
            if ":=" in window and PROXY_USE_RE.search(window):
                counts["reexport_proxy"] += 1
                examples["reexport_proxy"].append(f"{rel}:{i + 1}:{decl.group('name')}")

    print("Proof heartbeat")
    print("===============")
    print(f"root: {root}")
    for key in ["sorry", "proxy_field", "prop_socket", "reexport_proxy"]:
        print(f"{key}: {counts[key]}")
        for item in examples[key][: args.top]:
            print(f"  - {item}")
    print()
    print("Rule: prove from real lower lemmas, or leave an honest visible sorry; do not")
    print("replace missing mathematics by certificates, witness fields, or reexports.")
    return 1 if counts["sorry"] or counts["reexport_proxy"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
