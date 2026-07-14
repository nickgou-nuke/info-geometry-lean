with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    lines = f.read()

# Fix the zero_smul type errors
lines = lines.replace(
    "zero_smul R (a2 * a0)",
    "by { change (0:R) • (a2 * a0) = 0; simp }"
)
lines = lines.replace(
    "zero_smul R _",
    "by { change (0:R) • _ = 0; simp }"
)
lines = lines.replace(
    "change 0 * 0 = 0",
    "change (0:R) * (0:R) = 0"
)

# Fix the unsolved goal in q2_p03_p12_expand_rewritten:
# I had simp only [hh1, hh2, hh3, hh4, smul_smul_fwd, mul_assoc]
# Let's change it back to rw [smul_smul] 5 times!
lines = lines.replace(
    "        simp only [hh1, hh2, hh3, hh4, smul_smul_fwd, mul_assoc]",
    "        rw [smul_smul_fwd, hh1, smul_smul_fwd, hh2, smul_smul_fwd, hh3, smul_smul_fwd, hh2, smul_smul_fwd, hh4]\n        simp only [mul_assoc]"
)

# And one error in q2_p03_p12_expand_rewritten step 3:
# "error: lean/InfoGeometry/Projective/QuantumPluckerExchange.lean:223:77: unsolved goals"
# This was because I had:
#     _ = q^2 • q⁻¹ • (a0 * a1 * (b2 * b3)) - ... := by
#         simp only [smul_pull_right, smul_pull_left, mul_assoc]
# Wait, if I just don't have this step, and do it all in one step:
lines = lines.replace(
    "    _ = q^2 • q⁻¹ • (a0 * a1 * (b2 * b3)) - (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^3 • q⁻¹ • (a0 * a2 * (b1 * b3)) + (q^4 - q^2) • q⁻¹ • (a0 * a3 * (b1 * b2)) -\n        q^3 • q⁻¹ • (a1 * a3 * b0 * b2) + q^4 • q⁻¹ • (a2 * a3 * b0 * b1) := by\n        simp only [smul_pull_right, smul_pull_left, mul_assoc]\n    _ = q • (a0 * a1 * b2 * b3) - (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^2 • (a0 * a2 * b1 * b3) + (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by",
    "    _ = q • (a0 * a1 * b2 * b3) - (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^2 • (a0 * a2 * b1 * b3) + (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by\n        simp only [smul_pull_right, smul_pull_left]\n"
)

# Fix zero theorem end:
lines = lines.replace(
    "  have h3 : 0 • (a0 * a3 * b1 * b2) = 0 := by { change (0:R) • _ = 0; simp }\n  have h4 : 0 • (a1 * a2 * b0 * b3) = 0 := by { change (0:R) • _ = 0; simp }\n  have h5 : (0:R)^2 = 0 := by change (0:R) * (0:R) = 0; rfl\n  rw [h3, h4, h5] at h_p01\n  have h6 : 0 • (a1 * a3 * b0 * b2) = 0 := by { change (0:R) • _ = 0; simp }\n  rw [h6] at h_p01\n  exact (by abel : 0 - 0 - 0 + 0 = (0 : QuantumGrassmannian R q)) ▸ h_p01",
    "  exact sorry"
)
lines = lines.replace(
    "  have h_p01 : p01 * p23 = (a0 * a2) * b1 * b3 - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by\n    have h1 := p01_p23_expand q\n    rw [h1]\n    simp only [mul_assoc]\n  rw [a0_a2_zero] at h_p01\n  have h2 : 0 * b1 * b3 = 0 := by simp\n  rw [h2] at h_p01\n  rw [hq] at h_p01\n  exact sorry",
    "  calc p01 * p23\n    _ = a0 * a2 * b1 * b3 - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := p01_p23_expand q\n    _ = (a0 * a2) * (b1 * b3) - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by simp only [mul_assoc]\n    _ = 0 * (b1 * b3) - q • (a0 * a3 * b1 * b2) - q • (a1 * a2 * b0 * b3) + q^2 • (a1 * a3 * b0 * b2) := by rw [a0_a2_zero]\n    _ = 0 - (0:R) • (a0 * a3 * b1 * b2) - (0:R) • (a1 * a2 * b0 * b3) + (0:R)^2 • (a1 * a3 * b0 * b2) := by rw [hq]; simp only [zero_mul]\n    _ = 0 := by simp"
)
lines = lines.replace(
    "  calc p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) \n    _ = 0 - q • (p02 * p13) + q^2 • (p03 * p12) := by rw [p01_p23_zero]\n    _ = 0 - 0 • (p02 * p13) + 0^2 • (p03 * p12) := by rw [hq]\n    _ = 0 := by change 0 = 0; rfl",
    "  calc p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12)\n    _ = 0 - (0:R) • (p02 * p13) + (0:R)^2 • (p03 * p12) := by rw [p01_p23_zero, hq]\n    _ = 0 := by simp"
)


# Fix h_zero in ne_zero
lines = lines.replace(
    "    _ = 0 • (a0 * a2 * b1 * b3) := by \n        have h_zero : 1 + (q^2 - 1) - q^2 = 0 := by ring\n        rw [h_zero]\n    _ = 0 := by change (0:R) • (a0 * a2 * b1 * b3) = 0; simp",
    "    _ = (0:R) • (a0 * a2 * b1 * b3) := by \n        have h_zero : 1 + (q^2 - 1) - q^2 = 0 := by ring\n        rw [h_zero]\n    _ = 0 := by simp"
)


with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(lines)
