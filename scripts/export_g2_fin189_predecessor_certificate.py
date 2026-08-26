#!/usr/bin/env python3
"""Export CAS predecessor witnesses for the Lean 189-word flag table.

The search is performed in GAP on the exact translated Lean representatives.
The resulting witness relation is evidence for a later Lean certificate; this
script does not replace kernel proofs.
"""

from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
WORDS = ROOT / "lean/InfoGeometry/Algebra/Zorn/G2FlagWordCertificate.lean"
BASE = ROOT / "scripts/export_g2_flag_cell_witnesses.g"


def read_words():
    body = WORDS.read_text().split("def flagRepWords", 1)[1].split("def flagCells", 1)[0]
    entries = re.findall(r"(?m)^\s{2}(\[.*\])(?:,)?$", body)
    if len(entries) != 189:
        raise ValueError(f"expected 189 words, got {len(entries)}")
    pair = re.compile(r"\(\((\d+) : Fin 8\),\s*(-?\d+)\)")
    return [[(int(g) + 1, int(e)) for g, e in pair.findall(x)] for x in entries]


def source(words):
    rows = ["[" + ", ".join(f"[{g},{e}]" for g, e in reversed(w)) + "]" for w in words]
    return BASE.read_text() + "\n" + "\n".join([
        "leanWords := [", ",\n".join(rows), "];",
        "leanMatrices := List(leanWords, word -> Product(List(word, p -> flagWordGens[p[1]]^p[2])));",
        "for k in [1..12] do",
        "  cell := Q[k];",
        "  for i in cell do",
        "    found := fail;",
        "    for j in cell do",
        "      if j < i and found = fail then",
        "        for g in [1..8] do",
        "          if flagWordGens[g] * leanMatrices[j] = leanMatrices[i] then",
        "            found := [j-1,g-1]; break;",
        "          fi;",
        "        od;",
        "      fi;",
        "    od;",
        "    if found = fail then Error(""no predecessor for cell/index "", k, ""/"", i-1); fi;",
        "    Print(""FIN189_STEP "", k-1, "" "", i-1, "" "", found[1], "" "", found[2], ""\n"");",
        "  od;",
        "od;",
    ])


def main():
    with tempfile.NamedTemporaryFile("w", suffix=".g", delete=False) as f:
        f.write(source(read_words()))
        path = f.name
    result = subprocess.run(
        ["/home/goutev/miniforge3/envs/sage/bin/gap", "-q", path],
        cwd=ROOT, text=True, capture_output=True, check=True,
    )
    lines = [x for x in result.stdout.splitlines() if x.startswith("FIN189_STEP ")]
    if len(lines) != 189:
        raise RuntimeError(f"expected 189 predecessor witnesses, got {len(lines)}\n{result.stdout}")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
