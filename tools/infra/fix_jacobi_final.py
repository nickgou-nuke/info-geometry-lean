import re

with open("tools/infra/fix_jacobi_all.py", "r") as f:
    script = f.read()

# Fix types in the script string literals
script = script.replace("B.H => 1", "B.H => (1 : ℝ)")
script = script.replace("B.Ep => 1", "B.Ep => (1 : ℝ)")
script = script.replace("B.Em => 1", "B.Em => (1 : ℝ)")
script = script.replace("B.G1 => 1", "B.G1 => (1 : ℝ)")
script = script.replace("B.G2 => 1", "B.G2 => (1 : ℝ)")
script = script.replace("x => 0", "x => (0 : ℝ)")

# Add sum_B_eval
script = script.replace('basis_simp = "simp [bracket, Pi.single, Function.update, structConst]"',
                        'basis_simp = "simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num"')

# Make sure we don't double replace `x => 0` if it's not exactly that.
# Wait, let's just make sure it's valid Lean.
with open("tools/infra/fix_jacobi_all_2.py", "w") as f:
    f.write(script)

print("Done")
