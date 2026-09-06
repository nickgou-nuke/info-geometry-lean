import Mathlib.Analysis.Normed.Operator.Mul

/-!
# CBO-003: scalar and algebra multiplication adapters

AFP surface:

* `cblinfun_scaleC_right`;
* `cblinfun_scaleC_left`;
* `cblinfun_mult_right`;
* `cblinfun_mult_left`.

Lean owner surface:

* `ContinuousLinearMap.lsmul`;
* `ContinuousLinearMap.mul`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace ScalarMultiplication

variable {E A : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Scalar multiplication by a fixed complex number as a bounded operator. -/
def scalarOp (c : ℂ) : E →L[ℂ] E :=
  ContinuousLinearMap.lsmul ℂ ℂ c

@[simp]
theorem scalarOp_apply (c : ℂ) (x : E) :
    scalarOp (E := E) c x = c • x := by
  rfl

theorem norm_scalarOp_le (c : ℂ) :
    ‖scalarOp (E := E) c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_lsmul_apply_le c

section Algebra

variable [NonUnitalNormedRing A] [NormedSpace ℂ A]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- Left multiplication by a fixed algebra element. -/
def leftMul (a : A) : A →L[ℂ] A :=
  ContinuousLinearMap.mul ℂ A a

@[simp]
theorem leftMul_apply (a x : A) :
    leftMul a x = a * x := by
  rfl

theorem norm_leftMul_le (a : A) :
    ‖leftMul a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_mul_apply_le ℂ A a

/-- Right multiplication by a fixed algebra element. -/
def rightMul (a : A) : A →L[ℂ] A :=
  (ContinuousLinearMap.mul ℂ A).flip a

@[simp]
theorem rightMul_apply (a x : A) :
    rightMul a x = x * a := by
  rfl

theorem norm_rightMul_le (a : A) :
    ‖rightMul a‖ ≤ ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) ?_
  intro x
  simpa [rightMul_apply, mul_comm ‖x‖ ‖a‖] using norm_mul_le x a

end Algebra

end ScalarMultiplication
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

