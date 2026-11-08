with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Fix 658
text = text.replace("rw [Matrix.mul_apply]", "change Matrix.mul _ _ _ _ = _\n    rw [Matrix.mul_apply]")
text = text.replace("rw [PEquiv.toMatrix_mul_apply]", "change Matrix.mul _ _ _ _ = _\n    rw [PEquiv.toMatrix_mul_apply]")

with open("lean/DAG/MatrixGaussJordan.lean.tmp", "w") as f:
    f.write(text)
