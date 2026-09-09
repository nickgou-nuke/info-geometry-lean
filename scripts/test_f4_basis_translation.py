#!/usr/bin/env python3
"""Round-trip test for the F4 Lean/GAP label transport.

This checks only the finite generator-label interface.  It is deliberately
not a rank or linear-independence proof.
"""

from pathlib import Path
import subprocess
import tempfile

from translate_f4_basis import gap_to_lean, lean_label, lean_to_gap, read_lean


ROOT = Path(__file__).resolve().parent.parent
LEAN_OWNER = ROOT / "lean/InfoGeometry/Algebra/BaezF4H3Zorn.lean"
GAP_EXPORTER = ROOT / "scripts/export_f4_basis_gap.g"


def main() -> None:
    source_rows = read_lean(LEAN_OWNER)
    with tempfile.TemporaryDirectory() as directory:
        directory = Path(directory)
        lean_stream = directory / "lean_rows.g"
        lean_stream.write_text(lean_to_gap(LEAN_OWNER))
        recovered = gap_to_lean(lean_stream)
        assert recovered.count("(") == 52

        gap_output = directory / "gap_rows.g"
        gap_output.write_text(
            subprocess.run(
                ["gap", "-q", str(GAP_EXPORTER)],
                check=True,
                capture_output=True,
                text=True,
            ).stdout
        )
        gap_rows = []
        for line in gap_output.read_text().splitlines():
            fields = line.split()
            if len(fields) == 4 and fields[0] == "F4ROW" and fields[1].isdigit():
                gap_rows.append((int(fields[1]), fields[2], fields[3]))
        gap_rows = [(i, lean_label(a), lean_label(b)) for i, a, b in gap_rows]
        assert len(gap_rows) == 52
        assert [index for index, _, _ in gap_rows] == list(range(52))
        assert gap_rows == source_rows
    print("F4_BASIS_TRANSLATION_OK rows=52")


if __name__ == "__main__":
    main()
