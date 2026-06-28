import subprocess

LEAN_FILE = "lean/InfoGeometry/JordanDecomposition/Scratch.lean"

code = """import Mathlib

noncomputable section

open FiniteDimensional
open Submodule

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def NilpotentIndex (N : Module.End K V) (k : ℕ) : Prop :=
  (N ^ k) = 0 ∧ (N ^ (k - 1)) ≠ 0

lemma linearIndependent_cyclic [FiniteDimensional K V] (N : Module.End K V) (k : ℕ)
    (hN : NilpotentIndex N k) (x : V) (hx : (N ^ (k - 1)) x ≠ 0) :
    LinearIndependent K (fun (i : Fin k) => (N ^ (i : ℕ)) x) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  -- We want to prove c_j = 0 for all j. We do this by strong induction on k - 1 - j.
  sorry

"""

with open("/home/goutev/repos/info-geometry-lean/" + LEAN_FILE, "w") as f:
    f.write(code)

result = subprocess.run(["lake", "env", "lean", "--run", LEAN_FILE], cwd="/home/goutev/repos/info-geometry-lean", capture_output=True, text=True)
print(result.stdout + result.stderr)
