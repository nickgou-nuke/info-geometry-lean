import re

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# L27: simpa [findPivot, s, htop] using h
text = text.replace("simpa [findPivot, s, htop] using h", "simp only [findPivot, s, htop] at h\n    exact h")

# L230: simpa [ht] using hx
text = text.replace("simpa [ht] using hx", "simp only [ht] at hx\n    exact hx")

# Unused simp arguments
text = text.replace("simp only [hcol, ite_true, ite_eq_left]", "simp only [hcol, ite_true]") # wait, let's just use regex for unused simp arguments
text = text.replace("simp only [ite_eq_left rfl]", "simp only")
# Or I can just remove them manually.
