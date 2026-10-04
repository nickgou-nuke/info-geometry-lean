with open("lean/InfoGeometry/SplitOctonions/GradedBlades.lean", "r") as f:
    lines = f.readlines()

new_lines = []
for i, line in enumerate(lines):
    if line.startswith("theorem plucker_on_shell_quadric"):
        # Insert lemma before it
        new_lines.append("lemma blade1_mul_blade1_mul (u : V) (X : ExteriorAlgebra R V) :\n")
        new_lines.append("    blade1 R u * (blade1 R u * X) = 0 := by\n")
        new_lines.append("  rw [← mul_assoc, blade1_sq_zero R u, zero_mul]\n\n")
        
        # New proof
        new_lines.append(line)
        new_lines.append("    blade2 R u v * blade2 R u v = 0 := by\n")
        new_lines.append("  dsimp [blade2]\n")
        new_lines.append("  have h1 : blade1 R u * blade1 R v * (blade1 R u * blade1 R v) = blade1 R u * (blade1 R v * (blade1 R u * blade1 R v)) := by simp only [mul_assoc]\n")
        new_lines.append("  have h2 : blade1 R v * (blade1 R u * blade1 R v) = (blade1 R v * blade1 R u) * blade1 R v := by simp only [mul_assoc]\n")
        new_lines.append("  rw [h1, h2, blade1_swap_neg R v u]\n")
        new_lines.append("  simp only [neg_mul, mul_neg, mul_assoc]\n")
        new_lines.append("  rw [blade1_mul_blade1_mul R u]\n")
        new_lines.append("  simp only [neg_zero]\n")
        
        # Skip the old proof
        break
    else:
        new_lines.append(line)

# Also copy everything after the old plucker proof
in_plucker = False
for line in lines:
    if line.startswith("theorem plucker_on_shell_quadric"):
        in_plucker = True
    elif in_plucker and line.startswith("/-! ### 5."):
        in_plucker = False
    
    if in_plucker:
        continue
    if not in_plucker and line.startswith("/-! ### 5."):
        new_lines.append(line)
        in_plucker = False
    elif not in_plucker and line not in new_lines:
        new_lines.append(line)

with open("lean/InfoGeometry/SplitOctonions/GradedBlades.lean", "w") as f:
    f.writelines(new_lines)
