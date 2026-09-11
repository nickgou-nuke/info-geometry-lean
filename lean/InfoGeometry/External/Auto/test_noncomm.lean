import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

variable {F : Type*} [Field F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (ei ej : A_alg)

lemma test_noncomm : 
  (algebraMap F A_alg A + algebraMap F A_alg A⁻¹ * ei) * (algebraMap F A_alg A + algebraMap F A_alg A⁻¹ * ej) = 
  (algebraMap F A_alg A) * (algebraMap F A_alg A) +
    ((algebraMap F A_alg A⁻¹) * ei) * (algebraMap F A_alg A) +
    (((algebraMap F A_alg A) * ((algebraMap F A_alg A⁻¹) * ej)) +
      ((algebraMap F A_alg A⁻¹) * ei) * ((algebraMap F A_alg A⁻¹) * ej)) := by
  rw [mul_add]
  repeat rw [add_mul]
