import re

with open("TripotentTwistorDeRhamSynthesis.lean", "r") as f:
    content = f.read()

# 1
content = content.replace(
"""  · dsimp [v1]; rw [map_smul, map_add, hT3]
    rw [hT3, add_comm]""",
"""  · dsimp [v1]; rw [map_smul, map_add, hT3]
    have h_comm : T v + T (T v) = T (T v) + T v := by rw [add_comm]
    rw [h_comm]""")

# 2
content = content.replace(
"""  · dsimp [v_1]; rw [map_smul, map_sub, hT3]
    rw [hT3, ← neg_sub (T (T v)), smul_neg]""",
"""  · dsimp [v_1]; rw [map_smul, map_sub, hT3]
    have h_neg : T v - T (T v) = -(T (T v) - T v) := by rw [← neg_sub]
    rw [h_neg, smul_neg]""")

# 3
content = content.replace(
"""    _ = -Real.log p - -Real.log q - -q⁻¹ * (p - q) := by ring""",
"""    _ = -Real.log p - -Real.log q - -q⁻¹ * (p - q) := by ring
    _ = -Real.log p - -Real.log q - -(1 / q) * (p - q) := by rw [one_div]""")

with open("TripotentTwistorDeRhamSynthesis.lean", "w") as f:
    f.write(content)

