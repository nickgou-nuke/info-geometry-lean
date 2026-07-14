with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "r") as f:
    content = f.read()

# Fix hd rewrite
content = content.replace("simp only [hd]; field_simp; ring", "have : z' * M.c + M.d = 0 := by\n              calc z' * M.c + M.d = M.c * z' + M.d := by ring\n              _ = 0 := hd\n            rw [this]; field_simp; ring")

# Fix change issue. In the original, it was:
# change proj_cr (to_proj z1) (to_proj z2) (to_proj z3) (to_proj z4) = if factor * den1 = 0 then none else some (factor * num1 / (factor * den1))
# dsimp [proj_cr]
change_str = """change proj_cr (to_proj z1) (to_proj z2) (to_proj z3) (to_proj z4) = if factor * den1 = 0 then none else some (factor * num1 / (factor * den1))
  dsimp [proj_cr]"""

# We can replace this with a rewrite using the num_eq and den_eq we built up.
replacement = """have h_proj : proj_cr (to_proj (M.eval z1)) (to_proj (M.eval z2)) (to_proj (M.eval z3)) (to_proj (M.eval z4)) = if factor * den1 = 0 then none else some ((factor * num1) / (factor * den1)) := by
    dsimp [proj_cr]
    rw [num_eq, den_eq]
  rw [h_proj]"""

content = content.replace(change_str, replacement)

with open("lean/InfoGeometry/Topology/MobiusGeometry.lean", "w") as f:
    f.write(content)
