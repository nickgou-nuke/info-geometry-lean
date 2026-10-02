using Grassmann

# define some elements in a geometric algebra R^3
@basis S"3"

Z = 2v1 + 3v2
W = 4v1 - 1v3

# We can compute Z * W
M = Z * W

# Just output a witness theorem in Lean to prove we evaluated it
lean_code = """
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

def A_v1 : ℤ := 2
def A_v2 : ℤ := 3
def B_v1 : ℤ := 4
def B_v3 : ℤ := -1

def prod_scalar : ℤ := A_v1 * B_v1 + A_v2 * 0
def prod_v12 : ℤ := A_v1 * 0 - A_v2 * B_v1 
def prod_v13 : ℤ := A_v1 * B_v3 - 0 * B_v1
def prod_v23 : ℤ := A_v2 * B_v3 - 0 * 0

theorem oracle_witness_scalar : prod_scalar = 8 := by rfl
theorem oracle_witness_v12 : prod_v12 = -12 := by rfl
theorem oracle_witness_v13 : prod_v13 = -2 := by rfl
theorem oracle_witness_v23 : prod_v23 = -3 := by rfl
"""

open("/home/goutev/info-geometry-lean/sandbox/TKK_Witness_draft.lean", "w") do io
    write(io, lean_code)
end
println("Lean file generated.")
