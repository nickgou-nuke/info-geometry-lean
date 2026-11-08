import InfoGeometry.Clifford.ConformalTwistorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Conformal

open CliffordAlgebra
open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Riemannian

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/--
A conformal dilation by a scale factor `c` operates on the physical vector `x`.
In the Twistor / Conformal null cone embedding, this is realized as a linear 
transformation of the lift coordinates.
-/
def conformalDilation (c : R) (T : ConformalTwistorLift Q) : ConformalTwistorLift Q :=
  { x_phys := ⟨c • T.x_phys.val, Submodule.smul_mem _ c T.x_phys.property⟩,
    scale_inf := c * T.scale_inf,
    origin_comp := c * T.origin_comp }

/--
Theorem: Conformal dilations perfectly preserve the projective null cone boundary.
This formally verifies that scale transformations map physically null Twistor
lines to valid null Twistor lines natively in Mathlib.
-/
theorem dilation_preserves_null_cone (c : R) (T : ConformalTwistorLift Q)
    (h_null : T.isNull Q) : (conformalDilation Q c T).isNull Q := by
  dsimp [ConformalTwistorLift.isNull, conformalDilation]
  have h_mul : (c • T.x_phys.val) * (c • T.x_phys.val) = (c * c) • (T.x_phys.val * T.x_phys.val) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have h_mul_sub : ⟨(c • T.x_phys.val) * (c • T.x_phys.val), clMinus_mul_clMinus Q _ _ (Submodule.smul_mem (evenOdd Q 1) c T.x_phys.property) (Submodule.smul_mem (evenOdd Q 1) c T.x_phys.property)⟩ = (c * c) • (⟨T.x_phys.val * T.x_phys.val, clMinus_mul_clMinus Q _ _ T.x_phys.property T.x_phys.property⟩ : evenOdd Q 0) := by
    apply Subtype.ext
    exact h_mul
  rw [h_mul_sub, InfoGeometry.Riemannian.hTrace_smul Q (c * c)]
  rw [h_null]
  ring

end InfoGeometry.Clifford.Conformal
