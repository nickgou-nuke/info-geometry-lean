import subprocess
import os
import sys

def write_and_test(lean_code):
    with open('/home/goutev/auto/proofs/TestVirasoro.lean', 'w') as f:
        f.write(lean_code)
    result = subprocess.run(['lake', 'env', 'lean', '../proofs/TestVirasoro.lean'], cwd='/home/goutev/auto/lean_sandbox', capture_output=True, text=True)
    return result.returncode, result.stdout, result.stderr

lean_code = """
import Mathlib

abbrev VirasoroBasis := ℤ ⊕ Unit

variable (R : Type*) [CommRing R] [Invertible (12 : R)]

abbrev VirasoroModule := VirasoroBasis →₀ R

noncomputable def virasoroBracketBasis (x y : VirasoroBasis) : VirasoroModule R :=
  match x, y with
  | Sum.inl m, Sum.inl n =>
    let term1 := (m - n : R) • Finsupp.single (Sum.inl (m + n)) (1 : R)
    let term2 := if m + n = 0 then
                   (((m^3 - m : ℤ) : R) * ⅟(12 : R)) • Finsupp.single (Sum.inr ()) (1 : R)
                 else 0
    term1 + term2
  | _, _ => 0

lemma virasoroBracketBasis_self (x : VirasoroBasis) : virasoroBracketBasis R x x = 0 := by
  cases x with
  | inl m =>
    dsimp [virasoroBracketBasis]
    have : (m - m : R) = 0 := sub_self _
    rw [this, zero_smul]
    split
    · next h_eq =>
      have h0 : m = 0 := by omega
      subst h0
      have : (0^3 - 0 : ℤ) = 0 := by norm_num
      simp [this]
    · simp
  | inr c =>
    dsimp [virasoroBracketBasis]
    rfl
"""

ret, out, err = write_and_test(lean_code)
print(f"Ret: {ret}\nOut: {out}\nErr: {err}")
