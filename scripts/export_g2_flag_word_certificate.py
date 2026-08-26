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
    # GAP ExtRep is a matrix-product word.  Lean's automorphism carrier is
    # contravariant under matrix multiplication:
    #   autMatrix (f * g) = autMatrix g * autMatrix f.
    # Therefore the exact GAP word must be reversed when transported to the
    # Lean evaluator.  Generator numbering is GAP 1..8 versus Lean Fin 8.
    if len(extrep) % 2:
        raise ValueError("ExtRep must contain generator/exponent pairs")
    pairs = [
        f"(({extrep[i] - 1} : Fin 8), {extrep[i + 1]})"
        for i in range(len(extrep) - 2, -1, -2)
    ]
    return "[" + ", ".join(pairs) + "]"


def assert_transport_regression() -> None:
    """Check the non-commutative transport convention on the failing cell.

    This is deliberately a structural exporter check: GAP's word
    ``x₂⁻¹ x₈ x₇ x₈ x₇`` must become the reversed Lean list.  It does not
    claim the resulting word is a valid quotient representative; that claim
    belongs to a kernel-checked Lean owner theorem.
    """
    extrep_4_18 = [2, -1, 8, 1, 7, 1, 8, 1, 7, 1]
    expected = (
        "[((6 : Fin 8), 1), ((7 : Fin 8), 1), "
        "((6 : Fin 8), 1), ((7 : Fin 8), 1), ((1 : Fin 8), -1)]"
    )
    if lean_word(extrep_4_18) != expected:
        raise AssertionError("exact GAP→Lean anti-hom transport regression")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    assert_transport_regression()
    words, orbits = read_artifact(args.input)
    lines = [
        "/- Generated from the GAP ExtRep audit; propositions are intentionally not asserted here. -/",
        "import Mathlib.Data.Fin.Basic",
        "import Mathlib.Data.Matrix.Basic",
        "import Mathlib.Data.Finset.Basic",
        "import Mathlib.Data.ZMod.Basic",
        "import Mathlib.Tactic",
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
    lines += [
        "]",
        "",
        "/- GAP orbit order: 1,c,...,c^5,s,s*c,...,s*c^5. -/",
        "def flagWeyl : Fin 12 → (ZMod 6 × Bool) := ![",
        "  (0, false), (1, false), (2, false), (3, false), (4, false), (5, false),",
        "  (0, true), (1, true), (2, true), (3, true), (4, true), (5, true)",
        "]",
        "",
        "theorem flagWeyl_card : Fintype.card (Set.range flagWeyl) = 12 := by",
        "  have hinj : Function.Injective flagWeyl := by",
        "    decide",
        "  have hcard := Fintype.card_congr (Equiv.ofInjective flagWeyl hinj)",
        "  simpa using hcard.symm",
        "",
        "end InfoGeometry.Algebra.Zorn.G2FlagWordCertificate",
        "",
    ]
    args.output.write_text("\n".join(lines))


if __name__ == "__main__":
    main()
