import re

with open("lean/InfoGeometry/Categorical/MobiusGeometry.lean", "r") as f:
    content = f.read()

replacement = """theorem mobius_algebraic_decomposition (M : MobiusTransform) (hc : M.c ≠ 0) (z : ℂ)
    (hz : M.c * z + M.d ≠ 0) :
    (M.a * z + M.b) / (M.c * z + M.d) =
      M.a / M.c + ((M.b * M.c - M.a * M.d) / M.c^2) / (z + M.d / M.c) := by
  have hz' : z + M.d / M.c ≠ 0 := by
    intro h
    have h1 : M.c * (z + M.d / M.c) = M.c * 0 := by rw [h]
    rw [mul_zero] at h1
    have h2 : M.c * (z + M.d / M.c) = M.c * z + M.d := by
      calc M.c * (z + M.d / M.c) = M.c * z + M.c * (M.d / M.c) := by ring
      _ = M.c * z + M.d := by rw [mul_div_cancel₀ _ hc]
    rw [h2] at h1
    exact hz h1
  have hc2 : M.c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have h1 : M.c * (z + M.d / M.c) = M.c * z + M.d := by
    calc M.c * (z + M.d / M.c) = M.c * z + M.c * (M.d / M.c) := by ring
    _ = M.c * z + M.d := by rw [mul_div_cancel₀ M.d hc]
  have eq1 : ((M.b * M.c - M.a * M.d) / M.c ^ 2) / (z + M.d / M.c) = (M.b * M.c - M.a * M.d) / (M.c ^ 2 * (z + M.d / M.c)) := by
    rw [div_div]
  rw [eq1]
  have eq2 : M.c ^ 2 * (z + M.d / M.c) = M.c * (M.c * z + M.d) := by
    calc M.c ^ 2 * (z + M.d / M.c) = M.c * (M.c * (z + M.d / M.c)) := by ring
    _ = M.c * (M.c * z + M.d) := by rw [h1]
  rw [eq2]
  have eq3 : M.a / M.c = (M.a * (M.c * z + M.d)) / (M.c * (M.c * z + M.d)) := by
    have h_cancel : (M.a * (M.c * z + M.d)) / (M.c * (M.c * z + M.d)) = M.a / M.c := by
      rw [mul_div_mul_right M.a M.c hz]
    exact h_cancel.symm
  rw [eq3]
  rw [← add_div]
  have eq4 : (M.a * (M.c * z + M.d) + (M.b * M.c - M.a * M.d)) = M.c * (M.a * z + M.b) := by ring
  rw [eq4]
  have h_final : (M.c * (M.a * z + M.b)) / (M.c * (M.c * z + M.d)) = (M.a * z + M.b) / (M.c * z + M.d) := by
    rw [mul_div_mul_left (M.a * z + M.b) (M.c * z + M.d) hc]
  rw [h_final]"""

# Need to be careful. Let's find where the current broken theorem starts.
# We will just replace it correctly.
pattern = r"theorem mobius_algebraic_decomposition \([^)]+\) \([^)]+\) \([^)]+\)\s+\([^)]+\) :\s+\(M\.a \* z \+ M\.b\) / \(M\.c \* z \+ M\.d\) =\s+M\.a / M\.c \+ \(\(M\.b \* M\.c - M\.a \* M\.d\) / M\.c\^2\) / \(z \+ M\.d / M\.c\) := by\n(?:.|\n)*?exact \(mobius_decomposition_alt M\.a M\.b M\.c M\.d z hc hz'\)\.symm"

content = re.sub(pattern, replacement, content, flags=re.DOTALL)

with open("lean/InfoGeometry/Categorical/MobiusGeometry.lean", "w") as f:
    f.write(content)
