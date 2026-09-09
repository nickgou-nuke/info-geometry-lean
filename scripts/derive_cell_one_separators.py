#!/usr/bin/env python3
"""Derive Cell-1 separators on the exact imported Lean-word carrier."""
from pathlib import Path
import subprocess
import tempfile
from export_g2_lean_flag_witnesses import read_words, gap_source

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    source = gap_source(read_words()) + """
pc := Elements(Group(pcgens));
for target in [73,178] do
  residual := leanMatrices[25]^-1 * leanMatrices[target+1];
  Print("RESIDUAL ", target, "\\n");
  for i in [1..8] do
    for j in [1..8] do
      good := true;
      for u in pc do
        if residual[i][j] = u[i][j] then good := false; break; fi;
      od;
      if good then Print("SEPARATOR ", target, " ", i-1, " ", j-1, " value=", residual[i][j], "\\n"); fi;
    od;
  od;
od;
"""
    with tempfile.NamedTemporaryFile("w", suffix=".g", delete=False) as f:
        f.write(source)
        path = f.name
    result = subprocess.run(["/home/goutev/miniforge3/envs/sage/bin/gap", "-q", path],
                            cwd=ROOT, check=True, text=True, capture_output=True)
    print("\n".join(line for line in result.stdout.splitlines()
                     if line.startswith(("RESIDUAL", "SEPARATOR"))))

if __name__ == "__main__":
    main()
