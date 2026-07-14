with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    lines = f.read()

lines = lines.replace(
    "rw [smul_smul, smul_smul, smul_smul]",
    "rw [← smul_smul, ← smul_smul, ← smul_smul]"
)
lines = lines.replace(
    "rw [smul_smul, hh2, smul_smul, hh2]",
    "rw [← smul_smul, hh2, ← smul_smul, hh2]"
)
lines = lines.replace(
    "rw [smul_smul, smul_smul]",
    "rw [← smul_smul, ← smul_smul]"
)
lines = lines.replace(
    "rw [smul_smul, hh1, smul_smul, hh2, smul_smul, hh3, smul_smul, hh4]",
    "rw [← smul_smul, hh1, ← smul_smul, hh2, ← smul_smul, hh3, ← smul_smul, hh4]"
)

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(lines)
