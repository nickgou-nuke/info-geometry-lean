import re

with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "r") as f:
    content = f.read()

# Replace block 1: dsimp [P_plus...]; ring -> simp only [...]; ring_nf
simp_str = "simp only [P_plus, P_minus, matOneR, matJR, matKR, matOne, matJ, matK, Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one, smul_add, mul_add, add_mul, sub_eq_add_neg, neg_mul, mul_neg, neg_zero]"

# Find all lines like "  · dsimp [anything]; ring"
content = re.sub(r"· dsimp \[[^\]]+\]; ring", r"· " + simp_str + r"; ring_nf", content)

# Replace block 2: dsimp [...] at h -> simp only [...] at h
content = re.sub(r"dsimp \[matJR, matJ, Matrix.add_apply, Matrix.mul_apply, dotProduct, Matrix.zero_apply\] at h", simp_str + r" at h", content)

# Replace block 3: rw [h00]; ring -> rw [h00]; ring_nf
content = re.sub(r"· dsimp \[[^\]]+\]\n\s*rw \[h00\]; ring", r"· " + simp_str + r"\n    rw [h00]; ring_nf", content)
content = re.sub(r"· dsimp \[[^\]]+\]\n\s*rw \[h11\]; ring", r"· " + simp_str + r"\n    rw [h11]; ring_nf", content)

with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "w") as f:
    f.write(content)
