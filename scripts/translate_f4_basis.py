#!/usr/bin/env python3
"""Translate the explicit f4Basis index table between Lean and GAP.

This is a discovery-layer translator only.  It transports generator labels;
it does not certify coordinates, rank, or Lean theorem statements.
"""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path


BRANCH_RE = re.compile(r"(?ms)^\s*\|\s*(\d+)\s*=>\s*(.*?)(?=^\s*\|\s*\d+\s*=>|\Z)")
ARG_RE = re.compile(
    r"h3ZornJordanInnerDerivation\s*\((h3_diag[₁₂₃]|h3_off₁₂|h3_off₂₃|h3_off₃₁)"
    r"(?:\s+([0-7]))?\)\s*\((h3_diag_[123]|h3_off₁₂|h3_off₂₃|h3_off₃₁)"
    r"(?:\s+([0-7]))?\)"
)

GAP_RE = re.compile(r"^(\d+)\s+([^\s]+)\s+([^\s]+)$")
COORD_RE = re.compile(r"^F4COORDROW\s+(\d+)\s*:\s*\[(.*)\]$")
ACTION_RE = re.compile(r"^F4ACTIONROW\s+(\d+)\s*:\s*\[(.*)\]$")
PIVOT_RE = re.compile(r"^F4_ACTION_PIVOT\s+(\d+)\s*:\s*(\d+)\s*$")
MINOR_RE = re.compile(r"^F4_ACTION_MINOR_ROW\s+(\d+)\s*:\s*\[(.*)\]$")
GAP_TO_LEAN = {
    "diag1": "h3_diag₁", "diag2": "h3_diag₂", "diag3": "h3_diag₃",
    "off12": "h3_off₁₂", "off23": "h3_off₂₃", "off31": "h3_off₃₁",
}


def lean_label(label: str) -> str:
    if ":" in label:
        name, index = label.split(":", 1)
        return GAP_TO_LEAN.get(name, name) + ":" + index
    return GAP_TO_LEAN.get(label, label)


def read_lean(path: Path) -> list[tuple[int, str, str]]:
    text = path.read_text()
    body = text.split("def f4Basis", 1)[1]
    rows = []
    for branch in BRANCH_RE.finditer(body):
        index = int(branch.group(1))
        args = ARG_RE.search(branch.group(2))
        if args is None:
            continue
        left = args.group(1) + (":" + args.group(2) if args.group(2) else "")
        right = args.group(3) + (":" + args.group(4) if args.group(4) else "")
        rows.append((index, left, right))
    if len(rows) != 52 or [i for i, _, _ in rows] != list(range(52)):
        raise ValueError(f"expected Lean indices 0..51, got {len(rows)} rows")
    return rows


def lean_to_gap(path: Path) -> str:
    rows = read_lean(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    header = [
        "# INFO_GEOMETRY_F4_BASIS_EXPORT v1",
        "# source=Lean f4Basis",
        "# carrier=H3Zorn ℝ",
        "# generator=h3ZornJordanInnerDerivation",
        "# index_base=0",
        f"# source_sha256={digest}",
    ]
    return "\n".join(header + [f"F4ROW {i} {a} {b}" for i, a, b in rows]) + "\n"


def gap_to_lean(path: Path) -> str:
    rows = []
    lines = path.read_text().splitlines()
    if any(line.startswith("F4ROW") for line in lines):
        rows = []
        for line in lines:
            fields = line.split()
            if (len(fields) == 4 and fields[0] == "F4ROW"
                    and fields[1].isdigit()):
                rows.append((int(fields[1]), lean_label(fields[2]), lean_label(fields[3])))
    else:
        for line in lines:
            match = GAP_RE.match(line.strip())
            if match:
                rows.append((int(match.group(1)), lean_label(match.group(2)), lean_label(match.group(3))))
    if len(rows) != 52 or [i for i, _, _ in rows] != list(range(52)):
        raise ValueError("expected validated F4ROW indices 0..51")
    return "[\n" + ",\n".join(
        f"  ({i}, \"{a}\", \"{b}\")" for i, a, b in rows
    ) + "\n]\n"


def gap_coordinate_to_lean(path: Path) -> str:
    rows = []
    for line in path.read_text().splitlines():
        match = COORD_RE.match(line.strip())
        if match:
            entries = [entry.strip() for entry in match.group(2).split(",")]
            if len(entries) != 52:
                raise ValueError("each F4COORDROW must contain 52 entries")
            for entry in entries:
                if not re.fullmatch(r"-?\d+(?:/-?\d+)?", entry):
                    raise ValueError(f"non-rational coordinate: {entry}")
            rows.append((int(match.group(1)), entries))
    if len(rows) != 52 or [i for i, _ in rows] != list(range(52)):
        raise ValueError("expected F4COORDROW indices 0..51")
    return "def f4BasisCoordinateMatrix : Matrix (Fin 52) (Fin 52) ℚ :=\n  ![" + ",\n    ".join(
        "![" + ", ".join(entries) + "]" for _, entries in rows
    ) + "]\n"


def gap_action_to_lean(path: Path) -> str:
    rows = []
    for line in path.read_text().splitlines():
        match = ACTION_RE.match(line.strip())
        if match:
            entries = [entry.strip() for entry in match.group(2).split(",")]
            if len(entries) != 729:
                raise ValueError("each F4ACTIONROW must contain 729 entries")
            for entry in entries:
                if not re.fullmatch(r"-?\d+(?:/-?\d+)?", entry):
                    raise ValueError(f"non-rational action coordinate: {entry}")
            rows.append((int(match.group(1)), entries))
    if len(rows) != 52 or [i for i, _ in rows] != list(range(52)):
        raise ValueError("expected F4ACTIONROW indices 0..51")
    return "import Mathlib\n\n/-- Exact rational action-coordinate payload exported by the discovery layer.\nIt becomes mathematical evidence only after a Lean readback theorem connects it\nto the native `f4Basis` evaluator. -/\ndef f4BasisActionCoordinateMatrixQ : Matrix (Fin 52) (Fin 729) ℚ :=\n  ![" + ",\n    ".join(
        "![" + ", ".join(entries) + "]" for _, entries in rows
    ) + "]\n"


def gap_pivots_to_lean(path: Path) -> str:
    pivots = []
    for line in path.read_text().splitlines():
        match = PIVOT_RE.match(line.strip())
        if match:
            pivots.append((int(match.group(1)), int(match.group(2))))
        elif line.startswith("F4_ACTION_PIVOT_COLUMNS="):
            values = line.split("=", 1)[1].split(",")
            if any(not value.strip().isdigit() for value in values):
                raise ValueError("pivot columns must be decimal indices")
            pivots = [(i, int(value.strip())) for i, value in enumerate(values)]
    if len(pivots) != 52 or [i for i, _ in pivots] != list(range(52)):
        raise ValueError("expected F4_ACTION_PIVOT indices 0..51")
    columns = [c for _, c in pivots]
    if any(c >= 729 for c in columns) or len(set(columns)) != 52:
        raise ValueError("pivot columns must be distinct elements of Fin 729")
    return "def f4ActionPivot : Fin 52 → Fin 729 :=\n  ![" + ", ".join(
        f"⟨{c}, by omega⟩" for c in columns
    ) + "]\n"


def gap_minor_to_lean(path: Path) -> str:
    rows = []
    determinant = None
    for line in path.read_text().splitlines():
        if line.startswith("F4_ACTION_MINOR_DETERMINANT="):
            determinant = line.split("=", 1)[1].strip()
        match = MINOR_RE.match(line.strip())
        if match:
            entries = [entry.strip() for entry in match.group(2).split(",")]
            if len(entries) != 52:
                raise ValueError("each minor row must contain 52 entries")
            if any(not re.fullmatch(r"-?\d+(?:/-?\d+)?", entry)
                   for entry in entries):
                raise ValueError("minor entries must be rational literals")
            rows.append((int(match.group(1)), entries))
    if len(rows) != 52 or [i for i, _ in rows] != list(range(52)):
        raise ValueError("expected minor rows 0..51")
    if determinant is None or not re.fullmatch(r"-?\d+(?:/-?\d+)?", determinant):
        raise ValueError("missing exact minor determinant")
    return "import Mathlib\n\ndef f4ActionMinor : Matrix (Fin 52) (Fin 52) ℚ :=\n  ![" + ",\n    ".join(
        "![" + ", ".join(entries) + "]" for _, entries in rows
    ) + "]\n\ndef f4ActionMinorExpectedDeterminant : ℚ := " + determinant + "\n"


def main() -> None:
    if len(sys.argv) != 4 or sys.argv[1] not in {
        "lean-to-gap", "gap-to-lean", "gap-coordinate-to-lean",
        "gap-action-to-lean", "gap-pivots-to-lean", "gap-minor-to-lean"
    }:
        raise SystemExit("usage: translate_f4_basis.py MODE INPUT OUTPUT")
    mode, source, target = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
    if mode == "lean-to-gap":
        output = lean_to_gap(source)
    elif mode == "gap-to-lean":
        output = gap_to_lean(source)
    elif mode == "gap-coordinate-to-lean":
        output = gap_coordinate_to_lean(source)
    elif mode == "gap-action-to-lean":
        output = gap_action_to_lean(source)
    elif mode == "gap-pivots-to-lean":
        output = gap_pivots_to_lean(source)
    else:
        output = gap_minor_to_lean(source)
    target.write_text(output)


if __name__ == "__main__":
    main()
