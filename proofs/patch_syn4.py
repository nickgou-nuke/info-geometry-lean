import re

with open("TripotentTwistorDeRhamSynthesis.lean", "r") as f:
    content = f.read()

# 1. tripotent_trifurcation_vectors (sub_self issue)
content = content.replace(
"""    rw [h1, h2, zero_add, add_sub_cancel_right]""",
"""    rw [h1, h2]
    abel""")

# 2. Add_comm
content = content.replace(
"""    have : T (T v) + T (T (T v)) = T (T v) + T v := by rw [hT3]
    rw [this]""",
"""    have : T (T v) + T (T (T v)) = T v + T (T v) := by rw [hT3, add_comm]
    rw [this]""")

# 3. Neg sub
content = content.replace(
"""    have : T (T v) - T (T (T v)) = T (T v) - T v := by rw [hT3]
    rw [this, smul_sub, smul_sub, ← neg_sub, smul_neg]""",
"""    have : T (T v) - T (T (T v)) = T (T v) - T v := by rw [hT3]
    rw [this, ← neg_sub (T (T v)), smul_neg]""")

# 4. Itakura-Saito
content = content.replace(
"""  rw [Real.log_div hp' hq']
  ring""",
"""  rw [Real.log_div hp' hq']
  have h_q_inv : q * q⁻¹ = 1 := mul_inv_cancel hq'
  calc p / q - (Real.log p - Real.log q) - 1
    _ = p * q⁻¹ - Real.log p + Real.log q - 1 := by ring
    _ = p * q⁻¹ - Real.log p + Real.log q - q * q⁻¹ := by rw [h_q_inv]
    _ = -Real.log p - -Real.log q - -q⁻¹ * (p - q) := by ring""")

with open("TripotentTwistorDeRhamSynthesis.lean", "w") as f:
    f.write(content)

