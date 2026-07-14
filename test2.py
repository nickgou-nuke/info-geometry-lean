import re

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    text = f.read()

# Replace smul_pull_right and smul_pull_left with mathlib ones
text = text.replace("smul_pull_right", "Algebra.mul_smul_comm")
text = text.replace("smul_pull_left", "Algebra.smul_mul_assoc")

# Fix a3_a1 rewrite
text = text.replace("simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_assoc]", "simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_assoc]")

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(text)
