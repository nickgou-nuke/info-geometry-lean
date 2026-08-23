import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Regular representations of the Clifford even algebra

The even Clifford sector is an associative subalgebra.  Its regular
representations are kept algebraic here; analytic lifts belong to a concrete
finite-dimensional normed realization.
-/

namespace InfoGeometry.Clifford.EvenRegularRepresentation

open CliffordAlgebra

variable {R M : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

def leftMul (a : CliffordAlgebra.even Q) :
    CliffordAlgebra.even Q →ₗ[R] CliffordAlgebra.even Q where
  toFun x := a * x
  map_add' x y := by simp [mul_add]
  map_smul' r x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    calc
      a * (algebraMap R (CliffordAlgebra.even Q) r * x) =
          (a * algebraMap R (CliffordAlgebra.even Q) r) * x :=
        (mul_assoc _ _ _).symm
      _ = (algebraMap R (CliffordAlgebra.even Q) r * a) * x := by
        rw [(Algebra.commutes r a).symm]
      _ = algebraMap R (CliffordAlgebra.even Q) r * (a * x) :=
        mul_assoc _ _ _

def rightMul (a : CliffordAlgebra.even Q) :
    CliffordAlgebra.even Q →ₗ[R] CliffordAlgebra.even Q where
  toFun x := x * a
  map_add' x y := by simp [add_mul]
  map_smul' r x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    rw [mul_assoc]

@[simp] theorem leftMul_apply
    (a x : CliffordAlgebra.even Q) : leftMul Q a x = a * x := rfl

@[simp] theorem rightMul_apply
    (a x : CliffordAlgebra.even Q) : rightMul Q a x = x * a := rfl

theorem leftMul_comp
    (a b : CliffordAlgebra.even Q) :
    (leftMul Q a).comp (leftMul Q b) = leftMul Q (a * b) := by
  ext x
  simp [mul_assoc]

theorem rightMul_comp
    (a b : CliffordAlgebra.even Q) :
    (rightMul Q a).comp (rightMul Q b) = rightMul Q (b * a) := by
  ext x
  simp [mul_assoc]

theorem leftMul_rightMul_comm
    (a b : CliffordAlgebra.even Q) :
    (leftMul Q a).comp (rightMul Q b) =
      (rightMul Q b).comp (leftMul Q a) := by
  ext x
  simp [mul_assoc]

theorem leftMul_one :
    leftMul Q (1 : CliffordAlgebra.even Q) = LinearMap.id := by
  ext x
  simp

theorem rightMul_one :
    rightMul Q (1 : CliffordAlgebra.even Q) = LinearMap.id := by
  ext x
  simp

end InfoGeometry.Clifford.EvenRegularRepresentation

namespace InfoGeometry.Clifford.EvenRegularRepresentation

open CliffordAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)
variable [NormedAddCommGroup (CliffordAlgebra.even Q)]
variable [NormedSpace ℝ (CliffordAlgebra.even Q)]
variable [FiniteDimensional ℝ (CliffordAlgebra.even Q)]

noncomputable def leftMulContinuous
    (a : CliffordAlgebra.even Q) :
    CliffordAlgebra.even Q →L[ℝ] CliffordAlgebra.even Q :=
  LinearMap.toContinuousLinearMap (leftMul Q a)

noncomputable def rightMulContinuous
    (a : CliffordAlgebra.even Q) :
    CliffordAlgebra.even Q →L[ℝ] CliffordAlgebra.even Q :=
  LinearMap.toContinuousLinearMap (rightMul Q a)

@[simp] theorem leftMulContinuous_apply
    (a x : CliffordAlgebra.even Q) :
    leftMulContinuous Q a x = a * x := rfl

@[simp] theorem rightMulContinuous_apply
    (a x : CliffordAlgebra.even Q) :
    rightMulContinuous Q a x = x * a := rfl

theorem leftMulContinuous_comp
    (a b : CliffordAlgebra.even Q) :
    (leftMulContinuous Q a).comp (leftMulContinuous Q b) =
      leftMulContinuous Q (a * b) := by
  ext x
  simp [leftMulContinuous, leftMul, ContinuousLinearMap.comp_apply, mul_assoc]

theorem rightMulContinuous_comp
    (a b : CliffordAlgebra.even Q) :
    (rightMulContinuous Q a).comp (rightMulContinuous Q b) =
      rightMulContinuous Q (b * a) := by
  ext x
  simp [rightMulContinuous, rightMul, ContinuousLinearMap.comp_apply, mul_assoc]

end InfoGeometry.Clifford.EvenRegularRepresentation
