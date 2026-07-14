with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    lines = f.read()

# Restore expand_binomial
lines = lines.replace(
    "simp only [expand_binomial]",
    "rw [expand_binomial]"
)

# For q_p02_p13_expand
lines = lines.replace(
    "    _ = q • (a0 * b2 * (a1 * b3) - q • (a0 * b2 * (a3 * b1)) -\n             q • (a2 * b0 * (a1 * b3)) + q^2 • (a2 * b0 * (a3 * b1))) := by rw [expand_binomial]",
    "    _ = q • (a0 * b2 * (a1 * b3) - q • (a0 * b2 * (a3 * b1)) -\n             q • (a2 * b0 * (a1 * b3)) + q^2 • (a2 * b0 * (a3 * b1))) := by\n        have h_exp := expand_binomial (a0 * b2) (a2 * b0) (a1 * b3) (a3 * b1) q\n        rw [h_exp]"
)

# For q2_p03_p12_expand
lines = lines.replace(
    "    _ = q^2 • (a0 * b3 * (a1 * b2) - q • (a0 * b3 * (a2 * b1)) -\n               q • (a3 * b0 * (a1 * b2)) + q^2 • (a3 * b0 * (a2 * b1))) := by rw [expand_binomial]",
    "    _ = q^2 • (a0 * b3 * (a1 * b2) - q • (a0 * b3 * (a2 * b1)) -\n               q • (a3 * b0 * (a1 * b2)) + q^2 • (a3 * b0 * (a2 * b1))) := by\n        have h_exp := expand_binomial (a0 * b3) (a3 * b0) (a1 * b2) (a2 * b1) q\n        rw [h_exp]"
)

# Fix smul_smul directions
lines = lines.replace(
    "simp only [smul_smul, h2, h3, h4]",
    "rw [smul_smul, smul_smul, smul_smul]\n        rw [h2, h3]"
)
lines = lines.replace(
    "simp only [smul_smul, hh2]",
    "rw [smul_smul, hh2, smul_smul, hh2]"
)
lines = lines.replace(
    "simp only [smul_smul]",
    "rw [smul_smul]"
)
lines = lines.replace(
    "simp only [smul_smul, hh1, hh2, hh3, hh4]",
    "rw [smul_smul, hh1, smul_smul, hh2, smul_smul, hh3, smul_smul, hh2, smul_smul, hh4]"
)

# Fix q=0 case
lines = lines.replace(
    "_ = 0 := by exact rfl",
    "_ = 0 := by simp [sq]"
)
lines = lines.replace(
    "_ = 0 := by rw [zero_smul, zero_smul, sq, zero_mul, zero_smul, sub_zero, sub_zero, add_zero]",
    "_ = 0 := by simp [sq]"
)

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(lines)
