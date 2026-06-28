import re

with open("tools/infra/make_perfect_reconstruct.py", "r") as f:
    script = f.read()

# Fix the lack of real types in the functions
script = script.replace("B.H => 1", "B.H => (1 : ℝ)")
script = script.replace("B.Ep => 1", "B.Ep => (1 : ℝ)")
script = script.replace("B.Em => 1", "B.Em => (1 : ℝ)")
script = script.replace("B.G1 => 1", "B.G1 => (1 : ℝ)")
script = script.replace("B.G2 => 1", "B.G2 => (1 : ℝ)")
script = script.replace("x => 0", "x => (0 : ℝ)")

with open("tools/infra/make_perfect_reconstruct.py", "w") as f:
    f.write(script)

print("Done")
