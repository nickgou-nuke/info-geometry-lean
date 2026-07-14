import re

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    text = f.read()

# For q_p02_p13_expand
text = text.replace(
"""    _ = q • (a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * (a2 * b1) * b3)) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul, smul_pull_right, smul_pull_left]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a3 * (q⁻¹ • (b1 * b2))) -
        q^2 • ((q⁻¹ • (a1 * a2)) * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        rw [b2_b1 q hq, a2_a1 q hq]
        simp only [smul_sub, smul_pull_right, smul_pull_left, smul_smul_fwd]""",
"""    _ = q • (a0 * a1 * b2 * b3 - (q - q⁻¹) • (a0 * (a2 * b1) * b3)) - q^2 • (a0 * a3 * b2 * b1) -
        q^2 • (a2 * a1 * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul]
        rw [smul_pull_right (q - q⁻¹) a0 (a2 * b1), smul_pull_left (q - q⁻¹) (a0 * (a2 * b1)) b3]
    _ = q • (a0 * a1 * b2 * b3) - (q * (q - q⁻¹)) • (a0 * a2 * b1 * b3) - q^2 • (a0 * a3 * (q⁻¹ • (b1 * b2))) -
        q^2 • ((q⁻¹ • (a1 * a2)) * b0 * b3) + q^3 • (a2 * a3 * b0 * b1) := by
        rw [b2_b1 q hq, a2_a1 q hq]
        simp only [smul_sub]
        rw [smul_pull_right q⁻¹ (a0 * a3) (b1 * b2), smul_pull_left q⁻¹ (a1 * a2) (b0 * b3)]
        simp only [smul_smul_fwd]""")

# For q2_p03_p12_expand
text = text.replace(
"""    _ = q^2 • (a0 * a1 * b3 * b2) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + (q^3 * (q - q⁻¹)) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul, smul_pull_right, smul_pull_left, smul_sub, smul_smul_fwd]""",
"""    _ = q^2 • (a0 * a1 * b3 * b2) - (q^2 * (q - q⁻¹)) • (a0 * a3 * b1 * b2) -
        q^3 • (a0 * a2 * b3 * b1) + (q^3 * (q - q⁻¹)) • (a0 * a3 * b2 * b1) -
        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by
        simp only [mul_assoc, mul_sub, sub_mul, smul_sub]
        rw [smul_pull_right (q - q⁻¹) a0 (a3 * b1), smul_pull_left (q - q⁻¹) (a0 * (a3 * b1)) b2]
        rw [smul_pull_right (q - q⁻¹) a0 (a3 * b2), smul_pull_left (q - q⁻¹) (a0 * (a3 * b2)) b1]
        simp only [smul_smul_fwd]""")

# For q2_p03_p12_expand_rewritten
text = text.replace(
"""    _ = q^2 • (q⁻¹ • (a0 * a1 * (b2 * b3))) - (q^3 - q) • (a0 * a3 * (b1 * b2)) -
        q^3 • (q⁻¹ • (a0 * a2 * (b1 * b3))) + (q^4 - q^2) • (q⁻¹ • (a0 * a3 * (b1 * b2))) -
        q^3 • (q⁻¹ • ((a1 * a3) * b0 * b2)) + q^4 • (q⁻¹ • ((a2 * a3) * b0 * b1)) := by
        simp only [smul_pull_right, smul_pull_left]
    _ = q • (a0 * a1 * (b2 * b3)) - (q^3 - q) • (a0 * a3 * (b1 * b2)) -
        q^2 • (a0 * a2 * (b1 * b3)) + (q^3 - q) • (a0 * a3 * (b1 * b2)) -
        q^2 • ((a1 * a3) * b0 * b2) + q^3 • ((a2 * a3) * b0 * b1) := by
        simp only [smul_smul_fwd, hh1, hh2, hh3, hh4]""",
"""    _ = q^2 • (q⁻¹ • (a0 * a1 * (b2 * b3))) - (q^3 - q) • (a0 * a3 * (b1 * b2)) -
        q^3 • (q⁻¹ • (a0 * a2 * (b1 * b3))) + (q^4 - q^2) • (q⁻¹ • (a0 * a3 * (b1 * b2))) -
        q^3 • (q⁻¹ • ((a1 * a3) * b0 * b2)) + q^4 • (q⁻¹ • ((a2 * a3) * b0 * b1)) := by
        rw [smul_pull_right q⁻¹ a1 (b2 * b3), smul_pull_right q⁻¹ a0 (a1 * (b2 * b3))]
        rw [smul_pull_right q⁻¹ a2 (b1 * b3), smul_pull_right q⁻¹ a0 (a2 * (b1 * b3))]
        rw [smul_pull_right q⁻¹ a3 (b1 * b2), smul_pull_right q⁻¹ a0 (a3 * (b1 * b2))]
        rw [smul_pull_left q⁻¹ (a1 * a3) (b0 * b2)]
        rw [smul_pull_left q⁻¹ (a2 * a3) (b0 * b1)]
    _ = q • (a0 * a1 * (b2 * b3)) - (q^3 - q) • (a0 * a3 * (b1 * b2)) -
        q^2 • (a0 * a2 * (b1 * b3)) + (q^3 - q) • (a0 * a3 * (b1 * b2)) -
        q^2 • ((a1 * a3) * b0 * b2) + q^3 • ((a2 * a3) * b0 * b1) := by
        simp only [smul_smul_fwd, hh1, hh2, hh3, hh4]""")

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(text)
