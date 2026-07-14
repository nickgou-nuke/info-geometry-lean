with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    lines = f.read()

import re

new_zero_proof = """lemma quantumPlucker_of_q_zero (hq : q = 0) :
    p01 * p23 - q • (p02 * p13) + q^2 • (p03 * p12) = 0 := by
  have a0_a2_eq : a0 * a2 = q • (a2 * a0) := entry_sameRow R q 0 0 2 (by decide)
  have a0_a2_zero : a0 * a2 = 0 := by
    rw [a0_a2_eq, hq]
    exact zero_smul R (a2 * a0)
  have p01_p23_zero : p01 * p23 = 0 := by
    have h1 := p01_p23_expand q
    rw [h1]
    have h_assoc : a0 * a2 * b1 * b3 = (a0 * a2) * (b1 * b3) := by simp only [mul_assoc]
    rw [h_assoc, a0_a2_zero]
    simp only [zero_mul, sub_zero, zero_add]
    rw [hq]
    simp only [zero_smul, sq, zero_mul, sub_zero, zero_add]
  have hp02 : q • (p02 * p13) = 0 := by
    rw [hq]
    exact zero_smul R _
  have hp03 : q^2 • (p03 * p12) = 0 := by
    rw [hq]
    simp only [sq, zero_mul, zero_smul]
  rw [p01_p23_zero, hp02, hp03]
  simp only [sub_zero, add_zero]
"""

# replace quantumPlucker_of_q_zero
lines = re.sub(r"lemma quantumPlucker_of_q_zero.*?lemma quantumPlucker_of_q_ne_zero", new_zero_proof + "\nlemma quantumPlucker_of_q_ne_zero", lines, flags=re.DOTALL)

# For q2_p03_p12_expand_rewritten:
lines = lines.replace(
    "    _ = q^2 • (a0 * a1 * b3 * b2) - (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^3 • (a0 * a2 * b3 * b1) + (q^4 - q^2) • (a0 * a3 * b2 * b1) -\n        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by rw [h_exp]\n    _ = q^2 • (a0 * a1 * (q⁻¹ • (b2 * b3))) - (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^3 • (a0 * a2 * (q⁻¹ • (b1 * b3))) + (q^4 - q^2) • (a0 * a3 * (q⁻¹ • (b1 * b2))) -\n        q^3 • ((q⁻¹ • (a1 * a3)) * b0 * b2) + q^4 • ((q⁻¹ • (a2 * a3)) * b0 * b1) := by\n        rw [b3_b2 q hq, b3_b1 q hq, b2_b1 q hq, a3_a1 q hq, a3_a2 q hq]\n    _ = q • (a0 * a1 * b2 * b3) - (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^2 • (a0 * a2 * b1 * b3) + (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^2 • (a1 * a3 * b0 * b2) + q^3 • (a2 * a3 * b0 * b1) := by\n        simp only [smul_pull_right, smul_pull_left]",
    "    _ = q^2 • (a0 * a1 * b3 * b2) - (q^3 - q) • (a0 * a3 * b1 * b2) -\n        q^3 • (a0 * a2 * b3 * b1) + (q^4 - q^2) • (a0 * a3 * b2 * b1) -\n        q^3 • (a3 * a1 * b0 * b2) + q^4 • (a3 * a2 * b0 * b1) := by rw [h_exp]\n    _ = q^2 • (a0 * (a1 * (b3 * b2))) - (q^3 - q) • (a0 * (a3 * (b1 * b2))) -\n        q^3 • (a0 * (a2 * (b3 * b1))) + (q^4 - q^2) • (a0 * (a3 * (b2 * b1))) -\n        q^3 • (a3 * (a1 * (b0 * b2))) + q^4 • (a3 * (a2 * (b0 * b1))) := by simp only [mul_assoc]\n    _ = q^2 • (a0 * (a1 * (q⁻¹ • (b2 * b3)))) - (q^3 - q) • (a0 * (a3 * (b1 * b2))) -\n        q^3 • (a0 * (a2 * (q⁻¹ • (b1 * b3)))) + (q^4 - q^2) • (a0 * (a3 * (q⁻¹ • (b1 * b2)))) -\n        q^3 • ((q⁻¹ • (a1 * a3)) * (b0 * b2)) + q^4 • ((q⁻¹ • (a2 * a3)) * (b0 * b1)) := by\n        rw [b3_b2 q hq, b3_b1 q hq, b2_b1 q hq, a3_a1 q hq, a3_a2 q hq]\n    _ = q^2 • q⁻¹ • (a0 * (a1 * (b2 * b3))) - (q^3 - q) • (a0 * (a3 * (b1 * b2))) -\n        q^3 • q⁻¹ • (a0 * (a2 * (b1 * b3))) + (q^4 - q^2) • q⁻¹ • (a0 * (a3 * (b1 * b2))) -\n        q^3 • q⁻¹ • (a1 * (a3 * (b0 * b2))) + q^4 • q⁻¹ • (a2 * (a3 * (b0 * b1))) := by\n        simp only [smul_pull_right, smul_pull_left, mul_assoc]\n    _ = q • (a0 * (a1 * (b2 * b3))) - (q^3 - q) • (a0 * (a3 * (b1 * b2))) -\n        q^2 • (a0 * (a2 * (b1 * b3))) + (q^3 - q) • (a0 * (a3 * (b1 * b2))) -\n        q^2 • (a1 * (a3 * (b0 * b2))) + q^3 • (a2 * (a3 * (b0 * b1))) := by"
)

# Also fix the final rewrites of ne_zero
lines = lines.replace(
    "    _ = 0 := by change (0:R) • (a0 * a2 * b1 * b3) = 0; simp",
    "    _ = 0 := zero_smul R _"
)

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(lines)
