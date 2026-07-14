with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

# Replace the last part:
#   change proj_cr (to_proj z1) (to_proj z2) (to_proj z3) (to_proj z4) = if factor * den1 = 0 then none else some (factor * num1 / (factor * den1))
#   dsimp [proj_cr]
#   by_cases hden : den1 = 0

old_str = """  have h_proj : proj_cr (to_proj (M.eval z1)) (to_proj (M.eval z2)) (to_proj (M.eval z3)) (to_proj (M.eval z4)) = if factor * den1 = 0 then none else some ((factor * num1) / (factor * den1)) := by
    dsimp [proj_cr]
    rw [num_eq, den_eq]
  rw [h_proj]
  dsimp [proj_cr]
  by_cases hden : den1 = 0
  · have hden2 : factor * den1 = 0 := by rw [hden, mul_zero]
    rw [if_pos hden, if_pos hden2]
  · have hden2 : factor * den1 ≠ 0 := mul_ne_zero h_factor_ne_zero hden
    rw [if_neg hden, if_neg hden2]
    congr 1
    rw [mul_div_mul_left num1 den1 h_factor_ne_zero]"""

# Since I modified it with fix_cross_ratio3.py, let's just do a regex replace to catch the end of the proof.

import re
match = re.search(r"have h_proj : proj_cr.*mul_div_mul_left num1 den1 h_factor_ne_zero\]", content, re.DOTALL)
if match:
    new_str = """  have h_proj : proj_cr (to_proj (M.eval z1)) (to_proj (M.eval z2)) (to_proj (M.eval z3)) (to_proj (M.eval z4)) = if factor * den1 = 0 then none else some ((factor * num1) / (factor * den1)) := by
    dsimp [proj_cr]
    rw [num_eq, den_eq]
  rw [h_proj]
  dsimp [proj_cr]
  change (if den1 = 0 then none else some (num1 / den1)) = if factor * den1 = 0 then none else some ((factor * num1) / (factor * den1))
  by_cases hden : den1 = 0
  · have hden2 : factor * den1 = 0 := by rw [hden, mul_zero]
    rw [if_pos hden, if_pos hden2]
  · have hden2 : factor * den1 ≠ 0 := mul_ne_zero h_factor_ne_zero hden
    rw [if_neg hden, if_neg hden2]
    congr 1
    rw [mul_div_mul_left num1 den1 h_factor_ne_zero]"""
    content = content[:match.start()] + new_str + content[match.end():]

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
