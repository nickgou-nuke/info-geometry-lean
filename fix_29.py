with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# I will write a script to just replace simpa at 29, 50, 424, 918, 1559 to see what works.

text = text.replace("simpa [findPivot, s] using h", "simp only [findPivot, s] at h; exact h")
text = text.replace("simpa using (Finset.coe_min' hs)", "simp only at *; exact Finset.coe_min' hs")

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)
