import re

with open("lean/InfoGeometry/SplitOctonions/GradedBlades.lean", "r") as f:
    content = f.read()

# Fix blade1_swap_neg
content = content.replace(
    "exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)",
    "exact eq_neg_of_add_eq_zero_left (by rw [add_comm] at h; exact h)"
)

# Fix plucker_on_shell_quadric
old_plucker = """theorem plucker_on_shell_quadric (u v : V) :
    blade2 R u v * blade2 R u v = 0 := by
  dsimp [blade2]
  rw [mul_assoc (blade1 R u) (blade1 R v) _]
  rw [← mul_assoc (blade1 R v) (blade1 R u) (blade1 R v)]
  rw [blade1_swap_neg R v u]
  rw [neg_mul, mul_neg, ← mul_assoc (blade1 R u) (blade1 R u) _]
  rw [blade1_sq_zero R u, zero_mul, neg_zero]"""

new_plucker = """theorem plucker_on_shell_quadric (u v : V) :
    blade2 R u v * blade2 R u v = 0 := by
  dsimp [blade2]
  rw [mul_assoc, ← mul_assoc (blade1 R v)]
  rw [blade1_swap_neg R v u]
  simp only [neg_mul, mul_neg]
  rw [← mul_assoc (blade1 R u)]
  rw [blade1_sq_zero R u]
  simp only [zero_mul, neg_zero]"""

content = content.replace(old_plucker, new_plucker)

with open("lean/InfoGeometry/SplitOctonions/GradedBlades.lean", "w") as f:
    f.write(content)
