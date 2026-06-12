import Mathlib

variable {F : Type*} [Field F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (ei ej : A_alg)

lemma test2 : 
  (A • (1:A_alg) + A⁻¹ • ei) * (A⁻¹ • (1:A_alg) + A • ei) = 
  (A * A⁻¹) • (1:A_alg) + (A * A) • ei + (A⁻¹ * A⁻¹) • ei + (A * A⁻¹) • (ei * ei) := by
  rw [add_mul, mul_add, mul_add]
  simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_comm A⁻¹ A, add_assoc, add_left_comm, add_comm]
