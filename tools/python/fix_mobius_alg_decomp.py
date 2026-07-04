import re

with open("lean/InfoGeometry/Categorical/MobiusGeometry.lean", "r") as f:
    content = f.read()

replacement = """theorem mobius_algebraic_decomposition (M : MobiusTransform) (hc : M.c ≠ 0) (z : ℂ)
    (hz : M.c * z + M.d ≠ 0) :
    (M.a * z + M.b) / (M.c * z + M.d) =
      M.a / M.c + ((M.b * M.c - M.a * M.d) / M.c^2) / (z + M.d / M.c) := by
  have hz' : z + M.d / M.c ≠ 0 := by
    intro h
    have h2 : M.c * z + M.d = 0 := by
      calc M.c * z + M.d = M.c * z + M.c * (M.d / M.c) := by rw [mul_div_cancel₀ _ hc]
      _ = M.c * (z + M.d / M.c) := by ring
    have h1 : M.c * (z + M.d / M.c) = 0 := by rw [h, mul_zero]
    rw [h1] at h2
    exact hz h2
  exact (mobius_decomposition_alt M.a M.b M.c M.d z hc hz').symm"""

content = re.sub(r"theorem mobius_algebraic_decomposition.*?by\n  sorry", replacement, content, flags=re.DOTALL)

with open("lean/InfoGeometry/Categorical/MobiusGeometry.lean", "w") as f:
    f.write(content)
