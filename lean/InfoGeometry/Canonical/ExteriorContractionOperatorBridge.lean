/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ExteriorContractionOperatorBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Left contraction on the literal exterior algebra, implemented by the
zero-quadratic-form specialization of Mathlib's Clifford contraction. -/
def contractionOp (lambda : V →ₗ[R] R) : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) lambda

@[simp] theorem contraction_op_one (lambda : V →ₗ[R] R) :
    contractionOp lambda (1 : ExteriorAlgebra R V) = 0 :=
  CliffordAlgebra.contractLeft_one _ lambda

@[simp] theorem contraction_op_generator (lambda : V →ₗ[R] R) (v : V) :
    contractionOp lambda (ι R v) = algebraMap R (ExteriorAlgebra R V) (lambda v) :=
  CliffordAlgebra.contractLeft_ι _ lambda v

/-- The actual degree-lowering recurrence, including its graded minus sign. -/
theorem contraction_op_generator_mul (lambda : V →ₗ[R] R) (v : V)
    (omega : ExteriorAlgebra R V) :
    contractionOp lambda (ι R v * omega) =
      lambda v • omega - ι R v * contractionOp lambda omega :=
  CliffordAlgebra.contractLeft_ι_mul lambda v omega

/-- Mixed creation/contraction CAR on every exterior degree. -/
theorem contraction_op_mixed_car (lambda : V →ₗ[R] R) (v : V)
    (omega : ExteriorAlgebra R V) :
    contractionOp lambda (ι R v * omega) +
      ι R v * contractionOp lambda omega = lambda v • omega := by
  rw [contraction_op_generator_mul, sub_add_cancel]

/-- Evaluation on a normalized generator rules out the zero-operator proxy. -/
theorem contraction_op_ne_zero [Nontrivial R] (lambda : V →ₗ[R] R)
    (v : V) (hv : lambda v = 1) : contractionOp lambda ≠ 0 := by
  intro h
  have := congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f (ι R v)) h
  simpa [hv] using this

/-- **Theorem**: Global Contraction Annihilation Operator Nilpotency ι_λ² = 0 in End(⋀ V). -/
theorem contraction_op_sq_zero (lambda : V →ₗ[R] R) (omega : ExteriorAlgebra R V) :
    (contractionOp lambda) ((contractionOp lambda) omega) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft lambda omega

/-- **Theorem**: Global Contraction Annihilation Anti-Commutativity {ι_λ1, ι_λ2} = 0 in End(⋀ V). -/
theorem contraction_op_anticommute
    (lambda1 lambda2 : V →ₗ[R] R) (omega : ExteriorAlgebra R V) :
    (contractionOp lambda1) ((contractionOp lambda2) omega) +
    (contractionOp lambda2) ((contractionOp lambda1) omega) = 0 := by
  change CliffordAlgebra.contractLeft lambda1
      (CliffordAlgebra.contractLeft lambda2 omega) + _ = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

/-- **Theorem**: Master Exterior Contraction Global Operator CAR Synthesis.
    Unifies:
    1. Global contraction operator ι_λ ∈ End(⋀ V).
    2. Global contraction operator nilpotency ι_λ² = 0.
    3. Global contraction operator anti-commutativity {ι_λ1, ι_λ2} = 0 in End(⋀ V). -/
theorem master_exterior_contraction_operator_synthesis
    (lambda1 lambda2 : V →ₗ[R] R) (omega : ExteriorAlgebra R V) :
    ((contractionOp lambda1) ((contractionOp lambda1) omega) = 0) ∧
    ((contractionOp lambda1) ((contractionOp lambda2) omega) +
     (contractionOp lambda2) ((contractionOp lambda1) omega) = 0) := ⟨
  contraction_op_sq_zero lambda1 omega,
  contraction_op_anticommute lambda1 lambda2 omega
⟩

end InfoGeometry.Canonical.ExteriorContractionOperatorBridge
