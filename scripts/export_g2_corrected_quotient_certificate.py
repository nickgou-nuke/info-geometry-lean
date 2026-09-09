#!/usr/bin/env python3
"""Export the corrected G2(2) quotient representatives from the GAP audit.

This is a transport generator only.  It deliberately writes a separate
candidate carrier and never overwrites the legacy incidence-flag table.
The generated Lean file still requires kernel-checked matrix readback.
"""

from __future__ import annotations

import argparse
import ast
import re
import subprocess
from pathlib import Path


LINE = re.compile(r"^(FLAG_REP_EXT|CORRECTED_FLAG_ORBIT)_(\d+)=(.*)$")
FACTOR_LINE = re.compile(r"^(FLAG_CELL_(?:LEFT|RIGHT)_WITNESS)_(\d+)_(\d+)=(.*)$")


def collect(text: str) -> tuple[list[list[int]], list[list[int]]]:
    reps: dict[int, list[int]] = {}
    cells: dict[int, list[int]] = {}
    pending = ""
    kind = ""
    index = -1
    for raw in text.splitlines():
        if not pending:
            m = LINE.match(raw.strip())
            if m is None:
                continue
            kind, index_text, value = m.groups()
            index = int(index_text)
            pending = value.strip()
        else:
            pending += " " + raw.strip()
        if pending.count("[") != pending.count("]"):
            continue
        value = ast.literal_eval(pending)
        if kind == "FLAG_REP_EXT":
            reps[index] = value
        else:
            cells[index] = value
        pending = ""
    if sorted(reps) != list(range(189)):
        raise ValueError("GAP output did not contain 189 corrected representatives")
    if sorted(cells) != list(range(12)):
        raise ValueError("GAP output did not contain 12 corrected quotient cells")
    return [reps[i] for i in range(189)], [cells[i] for i in range(12)]


def collect_factors(text: str) -> tuple[dict[tuple[int, int], list[int]],
                                           dict[tuple[int, int], list[int]]]:
    factors: dict[str, dict[tuple[int, int], list[int]]] = {
        "FLAG_CELL_LEFT_WITNESS": {},
        "FLAG_CELL_RIGHT_WITNESS": {},
    }
    pending = ""
    kind = ""
    key = (-1, -1)
    for raw in text.splitlines():
        if not pending:
            match = FACTOR_LINE.match(raw.strip())
            if match is None:
                continue
            kind, k_text, i_text, value = match.groups()
            key = (int(k_text), int(i_text))
            pending = value.strip()
        else:
            pending += " " + raw.strip()
        if pending.count("[") != pending.count("]"):
            continue
        factors[kind][key] = ast.literal_eval(pending)
        pending = ""
    expected = set(factors["FLAG_CELL_LEFT_WITNESS"])
    if len(expected) != 189:
        raise ValueError("GAP output did not contain 189 factor rows")
    for kind, values in factors.items():
        if set(values) != expected:
            raise ValueError(f"GAP output did not contain all {kind} rows")
    return factors["FLAG_CELL_LEFT_WITNESS"], factors["FLAG_CELL_RIGHT_WITNESS"]


def lean_word(extrep: list[int]) -> str:
    if len(extrep) % 2:
        raise ValueError("ExtRep must contain generator/exponent pairs")
    pairs = [
        f"(({extrep[i] - 1} : Fin 8), {extrep[i + 1]})"
        for i in range(len(extrep) - 2, -1, -2)
    ]
    return "[" + ", ".join(pairs) + "]"


def render(reps: list[list[int]], cells: list[list[int]],
           left: dict[tuple[int, int], list[int]],
           right: dict[tuple[int, int], list[int]]) -> str:
    rep_rows = ",\n  ".join(lean_word(row) for row in reps)
    cell_rows = ",\n  ".join(
        "{" + ", ".join(str(x - 1) for x in row) + "}"
        for row in cells
    )
    factor_keys = sorted(left)
    left_rows = ",\n  ".join(
        f"(({k} : Fin 12), ({i} : Fin 189), {lean_word(left[(k, i)])})"
        for k, i in factor_keys
    )
    right_rows = ",\n  ".join(
        f"(({k} : Fin 12), ({i} : Fin 189), {lean_word(right[(k, i)])})"
        for k, i in factor_keys
    )
    return f'''import InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

/-! Generated candidate data from `verify_g2_true_bruhat_cover.g`.

This file is intentionally a separate carrier.  It is not imported by the
main build until its matrix and quotient readback theorems are proved.
-/

namespace InfoGeometry.Algebra.Zorn.G2CorrectedQuotientCertificate

open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

def correctedQuotientRepWords : Fin 189 → List (Fin 8 × Int) := ![
  {rep_rows}
]

def correctedQuotientCells : Fin 12 → Finset (Fin 189) := ![
  {cell_rows}
]

def correctedLeftWitness : List (Fin 12 × Fin 189 × List (Fin 8 × Int)) := [
  {left_rows}
]

def correctedRightWitness : List (Fin 12 × Fin 189 × List (Fin 8 × Int)) := [
  {right_rows}
]

end InfoGeometry.Algebra.Zorn.G2CorrectedQuotientCertificate
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    gap = root / "scripts/export_g2_flag_cell_witnesses.g"
    result = subprocess.run(
        ["/home/goutev/miniforge3/envs/sage/bin/gap", "-q"],
        input=gap.read_text(), text=True, capture_output=True, check=True,
    )
    reps, cells = collect(result.stdout)
    left, right = collect_factors(result.stdout)
    args.output.write_text(render(reps, cells, left, right))
    print(f"wrote corrected quotient candidate: {args.output}")


if __name__ == "__main__":
    main()
