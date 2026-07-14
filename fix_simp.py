with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    lines = f.read()
lines = lines.replace(
    "rw [smul_pull_left, smul_pull_right, smul_smul_fwd]",
    "simp only [smul_pull_left, smul_pull_right, smul_smul_fwd]"
)
with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(lines)
