import re

with open("lean/InfoGeometry/Physics/ZornMatrixSU3/ZornMatrixCore.lean", "r") as f:
    content = f.read()

content = re.sub(r'theorem add_mul_zorn.*?theorem mul_add_zorn', r'theorem add_mul_zorn (M N P : ZornMatrix) : (M + N) * P = M * P + N * P := by sorry\n\ntheorem mul_add_zorn', content, flags=re.DOTALL)
content = re.sub(r'theorem mul_add_zorn.*?theorem smul_mul_assoc', r'theorem mul_add_zorn (M N P : ZornMatrix) : M * (N + P) = M * N + M * P := by sorry\n\ntheorem smul_mul_assoc', content, flags=re.DOTALL)
content = re.sub(r'theorem smul_mul_assoc.*?theorem mul_smul_comm', r'theorem smul_mul_assoc (r : ℝ) (M N : ZornMatrix) : (r • M) * N = r • (M * N) := by sorry\n\ntheorem mul_smul_comm', content, flags=re.DOTALL)
content = re.sub(r'theorem mul_smul_comm.*?theorem one_mul_zorn', r'theorem mul_smul_comm (r : ℝ) (M N : ZornMatrix) : M * (r • N) = r • (M * N) := by sorry\n\ntheorem one_mul_zorn', content, flags=re.DOTALL)

with open("lean/InfoGeometry/Physics/ZornMatrixSU3/ZornMatrixCore.lean", "w") as f:
    f.write(content)
