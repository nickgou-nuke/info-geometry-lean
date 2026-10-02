with open("lean/InfoGeometry/GrandUnification/CantorTypeDBitwordLimit.lean", "r") as f:
    c = f.read()

bad = """      split_ifs with h
      · exfalso; exact h_not h
      · rfl"""

good = "      simp [h_not]"

c = c.replace(bad, good)
with open("lean/InfoGeometry/GrandUnification/CantorTypeDBitwordLimit.lean", "w") as f:
    f.write(c)
