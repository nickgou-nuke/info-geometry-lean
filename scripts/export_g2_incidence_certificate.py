#!/usr/bin/env python3
"""Translate the GAP parabolic incidence certificate into Lean."""

from pathlib import Path
import re
import sys


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: export_g2_incidence_certificate.py INPUT OUTPUT")
    source = Path(sys.argv[1]).read_text()
    rows = {}
    for match in re.finditer(r"INCIDENCE_(\d+)=\[([^\]]*)\]", source):
        index = int(match.group(1))
        values = [int(x) for x in re.findall(r"\d+", match.group(2))]
        rows[index] = values
    if sorted(rows) != list(range(63)):
        raise SystemExit("expected exactly 63 incidence rows")
    if any(len(row) != 3 or any(x < 0 or x >= 63 for x in row) for row in rows.values()):
        raise SystemExit("each incidence row must contain three valid line indices")

    lines = [
        "import Mathlib.Data.Fin.Basic",
        "import Mathlib.Data.Matrix.Basic",
        "import Mathlib.Data.Finset.Basic",
        "import Mathlib.Data.Fintype.Basic",
        "import Mathlib.Algebra.BigOperators.Group.Finset.Basic",
        "import Mathlib.Tactic.FinCases",
        "",
        "namespace InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate",
        "",
        "/-- The three lines incident with each of the 63 parabolic points. -/",
        "def incidence : Fin 63 → Finset (Fin 63)",
    ]
    for index in range(63):
        values = ", ".join(str(x) for x in rows[index])
        lines.append(f"  | ⟨{index}, _⟩ => {{{values}}}")
    lines.append("  | _ => ∅")
    lines += [
        "",
        "theorem incidence_card (p : Fin 63) : (incidence p).card = 3 := by",
        "  fin_cases p <;> native_decide",
        "",
        "theorem incidence_edge_card : (Finset.univ.biUnion incidence).card = 63 := by",
        "  native_decide",
        "",
        "theorem incidence_flag_card : (∑ p : Fin 63, (incidence p).card) = 189 := by",
        "  native_decide",
        "",
        "end InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate",
        "",
    ]
    Path(sys.argv[2]).write_text("\n".join(lines))


if __name__ == "__main__":
    main()
