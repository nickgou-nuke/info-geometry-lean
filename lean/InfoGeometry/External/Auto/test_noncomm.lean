import Mathlib

variable {F : Type*} [Field F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (ei ej : A_alg)

lemma test_noncomm : 
  (algebraMap F A_alg A + algebraMap F A_alg A⁻¹ * ei) * (algebraMap F A_alg A + algebraMap F A_alg A⁻¹ * ej) = 
  algebraMap F A_alg (A^2) + algebraMap F A_alg 1 * ei + algebraMap F A_alg 1 * ej + algebraMap F A_alg (A⁻¹^2) * ei * ej := by
  noncomm_ring
