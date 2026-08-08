import re

with open("TripotentTwistorDeRhamSynthesis.lean", "r") as f:
    content = f.read()

content = content.replace(
"""    have : T (T v) + T (T (T v)) = T v + T (T v) := by rw [hT3, add_comm]
    rw [this]""",
"""    rw [hT3, add_comm]""")

content = content.replace(
"""    have : T (T v) - T (T (T v)) = T (T v) - T v := by rw [hT3]
    rw [this, ← neg_sub (T (T v)), smul_neg]""",
"""    rw [hT3, ← neg_sub (T (T v)), smul_neg]""")

content = content.replace(
"""  have h_q_inv : q * q⁻¹ = 1 := mul_inv_cancel hq'""",
"""  have h_q_inv : q * q⁻¹ = 1 := mul_inv_cancel₀ hq'""")

with open("TripotentTwistorDeRhamSynthesis.lean", "w") as f:
    f.write(content)

