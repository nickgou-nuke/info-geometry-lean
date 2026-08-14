import re

with open('lean/InfoGeometry/Physics/HestenesKreinOperatorCalculus.lean', 'r') as f:
    content = f.read()

new_thm = """theorem anticommuting_mixed_square (I K : A) 
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1) (h_anti : I * K = - (K * I)) (θ η : ℝ) :
    (θ • I + η • K) ^ 2 = (η ^ 2 - θ ^ 2) • (1 : A) := by
  have h_I_sq : I * I = -1 := by
    calc I * I = I ^ 2 := by ring
    _ = -1 := hI
  have h_K_sq : K * K = 1 := by
    calc K * K = K ^ 2 := by ring
    _ = 1 := hK
  calc (θ • I + η • K) ^ 2 = (θ • I + η • K) * (θ • I + η • K) := by ring
    _ = θ^2 • (I * I) + (θ * η) • (I * K) + (η * θ) • (K * I) + η^2 • (K * K) := by
      sorry
    _ = θ^2 • (-1 : A) + (θ * η) • (I * K) + (θ * η) • (K * I) + η^2 • (1 : A) := by
      sorry
    _ = -θ^2 • (1 : A) + (θ * η) • (I * K + K * I) + η^2 • (1 : A) := by
      sorry
    _ = -θ^2 • (1 : A) + (θ * η) • (0 : A) + η^2 • (1 : A) := by
      sorry
    _ = (η^2 - θ^2) • (1 : A) := by
      sorry"""

content = re.sub(r"theorem anticommuting_mixed_square.*?trivial", new_thm, content, flags=re.DOTALL)

with open('lean/InfoGeometry/Physics/HestenesKreinOperatorCalculus.lean', 'w') as f:
    f.write(content)
