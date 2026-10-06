import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Remove empty simps
text = re.sub(r"^[ \t]*simp only[ \t]*\n", "", text, flags=re.MULTILINE)
text = re.sub(r"^[ \t]*simp only at hE[ \t]*\n", "", text, flags=re.MULTILINE)

# The goal is pivotRow <= pivotRow.
# In go_pivotRow_le_output, case 4:
text = text.replace("rw [dite_eq_right hpr]\n  · rename_i", "rw [dite_eq_right hpr]\n    omega\n  · rename_i")
# In go_pivotRow_le_output, case 5:
text = text.replace("rw [gaussJordanElimFull.go, dite_eq_right hcol]\n\nnoncomputable", "rw [gaussJordanElimFull.go, dite_eq_right hcol]\n    omega\n\nnoncomputable")

# There is also an error at line 1750, 1757, 1776, 1788.
# These are in go_all_invertible.
# The errors "simp made no progress" are because I didn't delete all empty simps, some had arguments maybe?
# The errors were: `error: lean/DAG/MatrixGaussJordan.lean:1750:4: `simp` made no progress`
# Wait, let's see what is on line 1750.

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
