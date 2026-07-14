import re

with open("lean/InfoGeometry/Projective/Sandbox/QuantumPluckerExchange.lean", "r") as f:
    text = f.read()

# Replace q_p02_p13_expand line 179
text = text.replace(
    "rw [hh1, smul_smul_fwd, hh2, smul_smul_fwd, hh2]",
    "rw [hh1, smul_smul_fwd q^2 q⁻¹ (a0 * a3 * b1 * b2), hh2, smul_smul_fwd q^2 q⁻¹ (a1 * a2 * b0 * b3), hh2]"
)

# Replace q2_p03_p12_expand line 198
text = text.replace(
    "rw [smul_smul_fwd, h3, smul_smul_fwd, h3, smul_smul_fwd, h4]",
    "rw [smul_smul_fwd q^2 q (a0 * b3 * a2 * b1), h3, smul_smul_fwd q^2 q (a3 * b0 * a1 * b2), h3, smul_smul_fwd q^2 q^2 (a3 * b0 * a2 * b1), h4]"
)

# Wait, in q2_p03_p12_expand there is `a0 * (b3 * a2) * b1` which expands to `a0 * b3 * a2 * b1`!
# Let's just use `smul_smul` from Mathlib directly using `rw [smul_smul q^2 q⁻¹, smul_smul q^2 q⁻¹]` !
# Mathlib's `smul_smul` doesn't require `A` to be explicit!
