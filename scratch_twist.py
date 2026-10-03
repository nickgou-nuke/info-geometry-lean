import re

with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "r") as f:
    content = f.read()

# insert the lemma
lemma = """
lemma mul_fin_two {α : Type*} [AddCommMonoid α] [Mul α] (A B : Matrix (Fin 2) (Fin 2) α) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  simp [Matrix.mul_apply, dotProduct, Fin.sum_univ_two]

"""
content = content.replace("local notation \"RealMat\" => Matrix (Fin 2) (Fin 2) ℝ\n", "local notation \"RealMat\" => Matrix (Fin 2) (Fin 2) ℝ\n" + lemma)

# replace instances of Matrix.mul_apply and dotProduct with mul_fin_two
content = content.replace("Matrix.mul_apply, dotProduct", "mul_fin_two")

with open("lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean", "w") as f:
    f.write(content)
