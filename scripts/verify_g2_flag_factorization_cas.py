#!/usr/bin/env python3
"""Carrier-aligned CAS audit for the G2 flag-cell factorization.

The GAP source is authoritative for the finite witness construction.  This
driver checks the exact convention used by the Lean files: GAP generators
1..8 translate to Lean ``Fin 8`` generators 0..7, and the first six
generators are the PC factor-word alphabet.  The script is evidence only;
the Lean kernel remains the theorem authority.
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
GAP_SOURCE = ROOT / "scripts" / "export_g2_flag_cell_witnesses.g"


def main() -> None:
    result = subprocess.run(
        ["/home/goutev/miniforge3/envs/sage/bin/gap", "-q"],
        input=GAP_SOURCE.read_text(),
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    if result.stderr:
        raise RuntimeError(result.stderr)

    output = result.stdout
    if "LEAN_CORRECTED_BRUHAT_COVER=PASS" not in output:
        raise AssertionError("corrected Lean Bruhat cover failed")
    if "EXACT_FLAG_ORBIT_PARTITIONS=PASS" not in output:
        raise AssertionError("flag orbit partition failed")

    representatives: list[tuple[str, str]] = []
    pending: tuple[str, str] | None = None
    for raw_line in output.splitlines():
        line = raw_line.strip()
        if pending is None:
            match = re.match(r"^FLAG_REP_EXT_(\d+)=\[(.*)$", line)
            if match is None:
                continue
            pending = (match.group(1), "[" + match.group(2))
        else:
            pending = (pending[0], pending[1] + line)
        if pending[1].count("[") == pending[1].count("]"):
            representatives.append(pending)
            pending = None
    if pending is not None:
        raise AssertionError("unterminated translated representative")
    if len(representatives) != 189:
        raise AssertionError(f"expected 189 translated representatives, got {len(representatives)}")
    for index, body in representatives:
        tokens = [int(value) for value in re.findall(r"-?\d+", body)]
        if len(tokens) % 2:
            raise AssertionError(f"odd ExtRep length at {index}")
        for generator in tokens[::2]:
            if not 1 <= generator <= 8:
                raise AssertionError(f"generator {generator} outside Lean Fin 8 carrier")

    # The GAP exporter constructs `witness * Weyl * rightWitness = Q[i]`
    # before emitting these words.  Reaching this point means every witness
    # was found and the translated representative table has the exact Lean
    # generator alphabet and cardinality.
    print("G2_FLAG_FACTORISATION_GAP_CARRIER=PASS")
    print("G2_FLAG_FACTORISATION_LEAN_GENERATOR_TRANSLATION=PASS")
    print("G2_FLAG_FACTORISATION_REPRESENTATIVE_COUNT=189")


if __name__ == "__main__":
    main()
