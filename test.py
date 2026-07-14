import re

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    text = f.read()

# Fix hq2
text = text.replace("have hq2 : (0:R)^2 = 0 := by change (0:R) * (0:R) = 0; ring", "have hq2 : (0:R)^2 = 0 := by ring")

# Fix smul_smul
text = text.replace("rw [smul_smul_fwd, hh1, smul_smul_fwd, hh2, smul_smul_fwd, hh3, smul_smul_fwd, hh2, smul_smul_fwd, hh4]", "simp only [smul_smul, hh1, hh2, hh3, hh4]")

# Fix a3_a1 rewrite
text = text.replace("simp only [smul_pull_right, smul_pull_left]", "simp only [smul_pull_right, smul_pull_left, mul_assoc]")

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(text)
