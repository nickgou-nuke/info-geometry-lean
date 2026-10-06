import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# For lines like:
# rw [gaussJordanElimFull.go, dite_eq_left hcol]
# dsimp only
# rw [hfind]
# dsimp only
# simp only [hpr, hpv, dite_eq_left]
# Replace with just: rw [go_selected_pivot_step_eq Es hcol hfind hpr]
# Wait, if we just change all `rw [gaussJordanElimFull.go, dite_eq_left hcol]` to `rw [gaussJordanElimFull.go]; simp only [hcol, hfind, hpr, hpv, dite_eq_left, dite_eq_right]`?

# Let's just fix the `rw [gaussJordanElimFull.go, dite_eq_left hcol]` block by block, or just write a regex to replace `rw [gaussJordanElimFull.go, dite_eq_left hcol]` and subsequent dsimp/rw/simp lines with one simp.
text = re.sub(
    r"rw \[gaussJordanElimFull\.go, dite_eq_left hcol\]\n\s*dsimp only\n\s*rw \[h_?find\]\n\s*dsimp only\n\s*simp only \[([^\]]*)\]",
    r"rw [gaussJordanElimFull.go]\n    simp only [hcol, hfind, \1]",
    text
)
# What if hfind is missing because it's a no_pivot case?
text = re.sub(
    r"rw \[gaussJordanElimFull\.go, dite_eq_left hcol\]\n\s*dsimp only\n\s*rw \[h_?find\]\n\s*dsimp only",
    r"rw [gaussJordanElimFull.go]\n    simp only [hcol, hfind, dite_eq_left, dite_eq_right]",
    text
)

text = re.sub(
    r"rw \[gaussJordanElimFull\.go, dite_eq_right hcol\]",
    r"rw [gaussJordanElimFull.go]\n    simp only [hcol, dite_eq_right]",
    text
)

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
