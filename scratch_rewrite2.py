import re

with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "r") as f:
    content = f.read()

simp_str = "simp only [P_plus, P_minus, matOneR, matJR, matKR, matOne, matJ, matK, Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one, smul_add, mul_add, add_mul, sub_eq_add_neg, neg_mul, mul_neg, neg_zero]"

content = re.sub(r"· dsimp \[[^\]]+\]\n\s*ring", r"· " + simp_str + r"\n    ring_nf", content)

with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "w") as f:
    f.write(content)
