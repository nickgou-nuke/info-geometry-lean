/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import Mathlib.Tactic.NoncommRing

/-!
# Native contraction on the exterior algebra

Contraction acts on the actual exterior algebra by the native Clifford-algebra
construction at zero quadratic form. The mixed CAR and generator evaluation
identify this operator, in addition to its nilpotency and anticommutation.
The construction works over a commutative ring and in particular over `ℝ`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorContractionOperatorBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Contraction by a genuine linear functional on the exterior-algebra carrier. -/
def contractionOp (lambda : V →ₗ[R] R) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) lambda

/-- The exterior-algebra unit is annihilated by contraction. -/
@[simp] theorem contraction_op_one (lambda : V →ₗ[R] R) :
    contractionOp lambda (1 : ExteriorAlgebra R V) = 0 := by
  exact CliffordAlgebra.contractLeft_one (0 : QuadraticForm R V) lambda

/-- Contraction on a degree-one generator evaluates the functional. -/
@[simp] theorem contraction_on_generator (lambda : V →ₗ[R] R) (v : V) :
    contractionOp lambda (ι R v) = algebraMap R (ExteriorAlgebra R V) (lambda v) := by
  exact CliffordAlgebra.contractLeft_ι (0 : QuadraticForm R V) lambda v

/-- The left contraction rule for a generator multiplied by an arbitrary form. -/
theorem contraction_op_generator_mul
    (lambda : V →ₗ[R] R) (v : V) (omega : ExteriorAlgebra R V) :
    contractionOp lambda (ι R v * omega) =
      lambda v • omega - ι R v * contractionOp lambda omega := by
  exact CliffordAlgebra.contractLeft_ι_mul
    (Q := (0 : QuadraticForm R V)) lambda v omega

/-- The mixed CAR holds on every form, with the actual evaluation pairing. -/
theorem contraction_op_mixed_car
    (lambda : V →ₗ[R] R) (v : V) (omega : ExteriorAlgebra R V) :
    contractionOp lambda (ι R v * omega) +
      ι R v * contractionOp lambda omega = lambda v • omega := by
  rw [contraction_op_generator_mul]
  exact sub_add_cancel _ _

/-- The mixed CAR as an equality in the native endomorphism algebra. -/
theorem contraction_op_mixed_car_end (lambda : V →ₗ[R] R) (v : V) :
    contractionOp lambda * Algebra.lmul R (ExteriorAlgebra R V) (ι R v) +
      Algebra.lmul R (ExteriorAlgebra R V) (ι R v) * contractionOp lambda =
        lambda v • (1 : Module.End R (ExteriorAlgebra R V)) := by
  apply LinearMap.ext
  intro omega
  change contractionOp lambda (ι R v * omega) +
    ι R v * contractionOp lambda omega = lambda v • omega
  exact contraction_op_mixed_car lambda v omega

/-- Repeated contraction by the same functional is zero. -/
theorem contraction_op_sq_zero (lambda : V →ₗ[R] R) (omega : ExteriorAlgebra R V) :
    (contractionOp lambda) ((contractionOp lambda) omega) = 0 := by
  exact CliffordAlgebra.contractLeft_contractLeft
    (Q := (0 : QuadraticForm R V)) lambda omega

/-- Contractions by two functionals anticommute. -/
theorem contraction_op_anticommute
    (lambda1 lambda2 : V →ₗ[R] R) (omega : ExteriorAlgebra R V) :
    (contractionOp lambda1) ((contractionOp lambda2) omega) +
    (contractionOp lambda2) ((contractionOp lambda1) omega) = 0 := by
  change CliffordAlgebra.contractLeft lambda1
      (CliffordAlgebra.contractLeft lambda2 omega) +
    CliffordAlgebra.contractLeft lambda2
      (CliffordAlgebra.contractLeft lambda1 omega) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

/-- The contraction representation is faithful on linear functionals. -/
@[simp] theorem contraction_op_eq_zero_iff (lambda : V →ₗ[R] R) :
    contractionOp lambda = 0 ↔ lambda = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    have hv := congrArg
      (fun T : Module.End R (ExteriorAlgebra R V) => T (ι R v)) h
    have hs : algebraMap R (ExteriorAlgebra R V) (lambda v) = 0 := by
      simpa only [contraction_on_generator, LinearMap.zero_apply] using hv
    exact (ExteriorAlgebra.algebraMap_eq_zero_iff V (lambda v)).mp hs
  · rintro rfl
    exact map_zero (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)))

/-- A nonzero evaluated pairing witnesses a nonzero contraction operator. -/
theorem contraction_op_ne_zero_of_pairing
    (lambda : V →ₗ[R] R) (v : V) (h : lambda v ≠ 0) :
    contractionOp lambda ≠ 0 := by
  intro hz
  have hlambda := (contraction_op_eq_zero_iff lambda).mp hz
  apply h
  simpa only [LinearMap.zero_apply] using
    congrArg (fun f : V →ₗ[R] R => f v) hlambda

/-- A concrete real contraction cannot be the zero operator. -/
theorem real_contraction_nonzero :
    contractionOp (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ≠ 0 := by
  apply contraction_op_ne_zero_of_pairing _ (1 : ℝ)
  exact one_ne_zero

/-- The original nilpotency/anticommutation packet, now for native contraction. -/
theorem master_exterior_contraction_operator_synthesis
    (lambda1 lambda2 : V →ₗ[R] R) (omega : ExteriorAlgebra R V) :
    ((contractionOp lambda1) ((contractionOp lambda1) omega) = 0) ∧
    ((contractionOp lambda1) ((contractionOp lambda2) omega) +
     (contractionOp lambda2) ((contractionOp lambda1) omega) = 0) :=
  ⟨contraction_op_sq_zero lambda1 omega,
    contraction_op_anticommute lambda1 lambda2 omega⟩

end InfoGeometry.Canonical.ExteriorContractionOperatorBridge
