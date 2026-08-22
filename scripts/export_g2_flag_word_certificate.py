#!/usr/bin/env python3
"""Translate GAP ExtRep flag representatives into a Lean word table.

This is a transport tool only.  It does not assert membership, distinctness,
or coverage; those properties must be proved by Lean after evaluating the
generated words in the exact carrier API.
"""

from __future__ import annotations

import argparse
import ast
import re
from pathlib import Path


LINE = re.compile(r"^FLAG_REP_EXT_(\d+)=(.*)$")


def read_words(path: Path) -> list[list[int]]:
    found: dict[int, list[int]] = {}
    pending: str | None = None
    for raw in path.read_text().splitlines():
        if pending is None:
            match = LINE.match(raw.strip())
            if match is None:
                continue
            pending = f"{match.group(1)}={match.group(2).strip()}"
        else:
            pending += " " + raw.strip()
        if pending.count("[") != pending.count("]"):
            continue
        index_text, value_text = pending.split("=", 1)
        pending = None
        index = int(index_text)
        value = ast.literal_eval(value_text)
        if not isinstance(value, list) or any(not isinstance(x, int) for x in value):
            raise ValueError(f"invalid ExtRep at index {index}")
        if index in found:
            raise ValueError(f"duplicate ExtRep index {index}")
        if any(x == 0 or abs(x) > 8 for x in value[::2]):
            raise ValueError(f"invalid generator index at {index}: {value}")
        if len(value) % 2:
            raise ValueError(f"odd ExtRep length at index {index}")
        found[index] = value
    if sorted(found) != list(range(189)):
        raise ValueError("expected exactly FLAG_REP_EXT_0 through FLAG_REP_EXT_188")
    return [found[i] for i in range(189)]


def lean_word(extrep: list[int]) -> str:
    # GAP numbers generators from 1; the Lean evaluator will use Fin 8 indices.
    pairs = [f"(({extrep[i] - 1} : Fin 8), {extrep[i + 1]})" for i in range(0, len(extrep), 2)]
    return "[" + ", ".join(pairs) + "]"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    words = read_words(args.input)
    lines = [
        "/- Generated from the GAP ExtRep audit; propositions are intentionally not asserted here. -/",
        "import Mathlib.Data.Fin.Basic",
        "import Mathlib.Data.Matrix.Basic",
        "",
        "namespace InfoGeometry.Algebra.Zorn.G2FlagWordCertificate",
        "",
        "def flagRepWords : Fin 189 → List (Fin 8 × Int) := ![",
    ]
    lines += ["  " + lean_word(word) + ("," if i < 188 else "") for i, word in enumerate(words)]
    lines += ["]", "", "end InfoGeometry.Algebra.Zorn.G2FlagWordCertificate", ""]
    args.output.write_text("\n".join(lines))


if __name__ == "__main__":
    main()
