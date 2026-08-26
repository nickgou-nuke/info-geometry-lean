#!/usr/bin/env python3
"""Export GAP witnesses for the actual Lean flagRepWords table.

The Lean evaluator stores the anti-homomorphic transport of a GAP word, so
each Lean list is reversed before it is evaluated by GAP.  This tool never
uses Representative(Q[i]) as the target: it imports and evaluates the Lean
table, then factors those imported matrices in the fixed GAP carrier.
"""

from __future__ import annotations

import re
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_WORDS = ROOT / "lean/InfoGeometry/Algebra/Zorn/G2FlagWordCertificate.lean"
GAP_BASE = ROOT / "scripts/export_g2_flag_cell_witnesses.g"


def read_words() -> list[list[tuple[int, int]]]:
    text = LEAN_WORDS.read_text()
    body = text.split("def flagRepWords", 1)[1].split("def flagCells", 1)[0]
    entries = re.findall(r"(?m)^\s{2}(\[.*\])(?:,)?$", body)
    if len(entries) != 189:
        raise ValueError(f"expected 189 Lean words, got {len(entries)}")
    pair_re = re.compile(r"\(\((\d+) : Fin 8\),\s*(-?\d+)\)")
    words: list[list[tuple[int, int]]] = []
    for entry in entries:
        words.append([(int(g) + 1, int(e)) for g, e in pair_re.findall(entry)])
    return words


def gap_source(words: list[list[tuple[int, int]]]) -> str:
    rows = []
    for word in words:
        pairs = ", ".join(f"[{g},{e}]" for g, e in reversed(word))
        rows.append(f"  [{pairs}]")
    return "\n".join(
        [
            GAP_BASE.read_text(),
            "leanWords := [",
            ",\n".join(rows),
            "];",
            "leanMatrices := List(leanWords, word -> Product(List(word, p -> flagWordGens[p[1]]^p[2])));",
            "for target in [45,73,178] do",
            "  qpos := PositionProperty(Q, q -> leanMatrices[target+1] in q);",
            "  if qpos = fail then Error(\"Lean word is outside Q\"); fi;",
            "  witness := First(Elements(B), b -> b * correctedW[2] in Q[qpos]);",
            "  if witness = fail then Error(\"no left witness for imported Lean word\"); fi;",
            "  rightWitness := (witness * correctedW[2])^-1 * leanMatrices[target+1];",
            "  if not rightWitness in B then Error(\"no right witness for imported Lean word\"); fi;",
            "  # Anti-hom transport swaps the two factors in Lean's left*W*right form.",
            "  Print(\"LEAN_FLAG_LEFT_WITNESS_\", target, \"=\", fixedPCExtRep(rightWitness), \"\\n\");",
            "  Print(\"LEAN_FLAG_RIGHT_WITNESS_\", target, \"=\", fixedPCExtRep(witness), \"\\n\");",
            "od;",
        ]
    )


def main() -> None:
    source = gap_source(read_words())
    with tempfile.NamedTemporaryFile("w", suffix=".g", delete=False) as handle:
        handle.write(source)
        path = handle.name
    result = subprocess.run(
        ["/home/goutev/miniforge3/envs/sage/bin/gap", "-q", path],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    emitted = False
    for line in result.stdout.splitlines():
        if line.startswith("LEAN_FLAG_"):
            emitted = True
            print(line)
    if not emitted:
        raise RuntimeError(result.stdout + result.stderr)


if __name__ == "__main__":
    main()
