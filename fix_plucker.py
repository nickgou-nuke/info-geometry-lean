with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    lines = f.read()

# Fix expand_binomial
lines = lines.replace(
    "rw [expand_binomial]",
    "simp only [expand_binomial]"
)
lines = lines.replace(
    "rw [expand_binomial (a0 * b2) (a2 * b0) (a1 * b3) (a3 * b1) q]",
    "simp only [expand_binomial]"
)
lines = lines.replace(
    "rw [expand_binomial (a0 * b3) (a3 * b0) (a1 * b2) (a2 * b1) q]",
    "simp only [expand_binomial]"
)

# Fix smul_smul blocks
lines = lines.replace(
    "rw [← smul_smul, hh1, ← smul_smul, hh2, ← smul_smul, hh3, ← smul_smul, hh4]",
    "simp only [smul_smul, hh1, hh2, hh3, hh4]"
)
lines = lines.replace(
    "rw [← smul_smul, hh2, ← smul_smul, hh2]",
    "simp only [smul_smul, hh2]"
)
lines = lines.replace(
    "rw [← smul_smul, ← smul_smul, ← smul_smul]",
    "simp only [smul_smul, h2, h3, h4]"
)
lines = lines.replace(
    "rw [← smul_smul, ← smul_smul]",
    "simp only [smul_smul]"
)
lines = lines.replace(
    "rw [h3, h4]",
    ""
)
lines = lines.replace(
    "rw [h2, h3]",
    ""
)

# Fix q=0 case
lines = lines.replace(
    "_ = 0 := by rw [zero_smul, zero_smul, sq, zero_mul, zero_smul, sub_zero, sub_zero, add_zero]",
    "_ = 0 := by exact rfl"
)
lines = lines.replace(
    "_ = 0 := by rw [zero_smul, sq, zero_mul, zero_smul, sub_zero, add_zero]",
    "_ = 0 := by exact rfl"
)
lines = lines.replace(
    "_ = 0 := by rw [zero_smul]",
    "_ = 0 := by exact rfl"
)


with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(lines)
