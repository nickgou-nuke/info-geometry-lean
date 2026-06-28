import subprocess
import re
import sys

def check_code(code):
    with open("lean/InfoGeometry/JordanDecomposition/Scratch.lean", "w") as f:
        f.write(code)
    r = subprocess.run(["lake", "env", "lean", "--run", "lean/InfoGeometry/JordanDecomposition/Scratch.lean"], capture_output=True, text=True)
    return r.stdout + r.stderr

code = """import Mathlib
noncomputable section
open FiniteDimensional Submodule
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def NilpotentIndex (N : Module.End K V) (k : ℕ) : Prop := (N ^ k) = 0 ∧ (N ^ (k - 1)) ≠ 0

lemma linearIndependent_cyclic [FiniteDimensional K V] (N : Module.End K V) (k : ℕ)
    (hN : NilpotentIndex N k) (x : V) (hx : (N ^ (k - 1)) x ≠ 0) :
    LinearIndependent K (fun (i : Fin k) => (N ^ (i : ℕ)) x) := by
  sorry
"""

print(check_code(code))
