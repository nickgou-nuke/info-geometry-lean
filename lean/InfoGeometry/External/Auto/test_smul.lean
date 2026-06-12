import Mathlib

variable {F : Type*} [Field F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (ei ej : A_alg)

lemma test : (A • 1 : A_alg) * (A⁻¹ • ei) = (A * A⁻¹) • ei := by
  simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

