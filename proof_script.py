import subprocess
import time
import os

LEAN_FILE = "lean/InfoGeometry/JordanDecomposition/Scratch.lean"

def run_lean():
    result = subprocess.run(["lake", "env", "lean", "--run", LEAN_FILE], cwd="/home/goutev/repos/info-geometry-lean", capture_output=True, text=True)
    return result.stdout + result.stderr

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
  have h_all : ∀ (j : ℕ) (hj : j < k), c ⟨j, hj⟩ = 0 := by
    sorry
  intro i
  exact h_all i.val i.isLt
"""

with open("/home/goutev/repos/info-geometry-lean/" + LEAN_FILE, "w") as f:
    f.write(code)

print("Compiling lean file...")
output = run_lean()
print(output)
