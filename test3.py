import re

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "r") as f:
    text = f.read()

# Replace mathlib lemmas back to custom ones with explicit types
text = text.replace("""lemma smul_pull_left {A : Type u} [Ring A] [Algebra R A] (c : R) (x y : A) :
  (c • x) * y = c • (x * y) := Algebra.smul_mul_assoc c x y

lemma smul_pull_right {A : Type u} [Ring A] [Algebra R A] (c : R) (x y : A) :
  x * (c • y) = c • (x * y) := Algebra.mul_smul_comm c x y

lemma smul_smul_fwd {A : Type u} [Ring A] [Algebra R A] (c d : R) (x : A) :
  c • d • x = (c * d) • x := smul_smul c d x""", """lemma smul_pull_left (c : R) (x y : QuantumGrassmannian R q) :
  (c • x) * y = c • (x * y) := Algebra.smul_mul_assoc c x y

lemma smul_pull_right (c : R) (x y : QuantumGrassmannian R q) :
  x * (c • y) = c • (x * y) := Algebra.mul_smul_comm c x y

lemma smul_smul_fwd (c d : R) (x : QuantumGrassmannian R q) :
  c • d • x = (c * d) • x := smul_smul c d x""")

# Replace the mathlib lemma usages with the custom ones
text = text.replace("Algebra.mul_smul_comm", "smul_pull_right")
text = text.replace("Algebra.smul_mul_assoc", "smul_pull_left")
text = text.replace("simp only [smul_smul,", "simp only [smul_smul_fwd,")

with open("lean/InfoGeometry/Projective/QuantumPluckerExchange.lean", "w") as f:
    f.write(text)
