#!/usr/bin/env python3
"""Export the current Lean flagRepWords table as a GAP data include.

Lean evaluates a word as a left-to-right group product, while `autMatrix` is
contravariant.  GAP receives the reversed word so its ordinary matrix product
is the matrix of the Lean representative.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean/InfoGeometry/Algebra/Zorn/G2FlagWordCertificate.lean"
OUTPUT = ROOT / "scripts/generated_g2_lean_flag_words.g"


def table_body(text: str) -> str:
    marker = "def flagRepWords"
    start = text.index(":= ![", text.index(marker)) + len(":= ![")
    depth = 1
    pos = start
    while depth:
        if text[pos] == "[":
            depth += 1
        elif text[pos] == "]":
            depth -= 1
        pos += 1
    return text[start : pos - 1]


def top_level_words(body: str) -> list[str]:
    words: list[str] = []
    start = 0
    depth = 0
    for pos, char in enumerate(body):
        if char == "[":
            if depth == 0:
                start = pos
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                words.append(body[start : pos + 1])
    return words


def convert(word: str) -> str:
    pairs = [
        (int(generation) + 1, int(exponent))
        for generation, exponent in re.findall(
            r"\(\((\d+)\s*:\s*Fin 8\),\s*(-?\d+)\)", word
        )
    ]
    pairs.reverse()
    return "[" + ", ".join(f"[{g}, {e}]" for g, e in pairs) + "]"


def main() -> None:
    words = top_level_words(table_body(SOURCE.read_text()))
    if len(words) != 189:
        raise RuntimeError(f"expected 189 Lean words, got {len(words)}")
    lines = [
        "# Generated from the current Lean flagRepWords table.",
        "leanFlagWords := [",
    ]
    lines += [f"  {convert(word)}" + ("," if i < 188 else "") for i, word in enumerate(words)]
    lines += ["];"]
    OUTPUT.write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
