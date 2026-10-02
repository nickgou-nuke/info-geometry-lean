with open("lean/InfoGeometry/GrandUnification/CantorTypeDBitwordLimit.lean", "r") as f:
    c = f.read()

bad = "      simp [h_not]"
good = "      rw [dif_neg h_not]"

c = c.replace(bad, good)
with open("lean/InfoGeometry/GrandUnification/CantorTypeDBitwordLimit.lean", "w") as f:
    f.write(c)
