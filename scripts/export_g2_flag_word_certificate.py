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


LINE = re.compile(r"^(FLAG_REP_EXT|CORRECTED_FLAG_ORBIT)_(\d+)=(.*)$")


def read_artifact(path: Path) -> tuple[list[list[int]], list[list[int]]]:
    found: dict[int, list[int]] = {}
    orbits: dict[int, list[int]] = {}
    pending: str | None = None
    pending_kind: str | None = None
    for raw in path.read_text().splitlines():
        if pending is None:
            match = LINE.match(raw.strip())
            if match is None:
                continue
            pending_kind = match.group(1)
            pending = f"{match.group(2)}={match.group(3).strip()}"
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
        if pending_kind == "FLAG_REP_EXT":
            if index in found:
                raise ValueError(f"duplicate ExtRep index {index}")
            if any(x == 0 or abs(x) > 8 for x in value[::2]):
                raise ValueError(f"invalid generator index at {index}: {value}")
            if len(value) % 2:
                raise ValueError(f"odd ExtRep length at index {index}")
            found[index] = value
        else:
            if index in orbits:
                raise ValueError(f"duplicate orbit index {index}")
            if any(x < 1 or x > 189 for x in value):
                raise ValueError(f"invalid GAP coset index at orbit {index}")
            orbits[index] = value
    if sorted(found) != list(range(189)):
        raise ValueError("expected exactly FLAG_REP_EXT_0 through FLAG_REP_EXT_188")
    if sorted(orbits) != list(range(12)):
        raise ValueError("expected exactly CORRECTED_FLAG_ORBIT_0 through _11")
    return [found[i] for i in range(189)], [orbits[i] for i in range(12)]


def lean_word(extrep: list[int]) -> str:
    # GAP numbers generators from 1; the Lean evaluator will use Fin 8 indices.
    pairs = [f"(({extrep[i] - 1} : Fin 8), {extrep[i + 1]})" for i in range(0, len(extrep), 2)]
    return "[" + ", ".join(pairs) + "]"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    words, orbits = read_artifact(args.input)
    lines = [
        "/- Generated from the GAP ExtRep audit; propositions are intentionally not asserted here. -/",
        "import Mathlib.Data.Fin.Basic",
        "import Mathlib.Data.Matrix.Basic",
        "import Mathlib.Data.Finset.Basic",
        "",
        "namespace InfoGeometry.Algebra.Zorn.G2FlagWordCertificate",
        "",
        "def flagRepWords : Fin 189 → List (Fin 8 × Int) := ![",
    ]
    lines += ["  " + lean_word(word) + ("," if i < 188 else "") for i, word in enumerate(words)]
    lines += ["]", "", "def flagCells : Fin 12 → Finset (Fin 189) := !["]
    lines += [
        "  {" + ", ".join(str(i - 1) for i in orbit) + "}" + ("," if k < 11 else "")
        for k, orbit in enumerate(orbits)
    ]
    lines += ["]", "", "end InfoGeometry.Algebra.Zorn.G2FlagWordCertificate", ""]
    args.output.write_text("\n".join(lines))


if __name__ == "__main__":
    main()
