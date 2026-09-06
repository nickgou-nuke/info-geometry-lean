import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ExteriorContractionOperatorBridge

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Global Contraction Operator ι_λ on ExteriorAlgebra R V via Linear Maps. -/
def contractionOp (_lambda : V →ₗ[R] R) : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) _lambda

/-- **Theorem**: Global Contraction Annihilation Operator Nilpotency ι_λ² = 0 in End(⋀ V). -/
theorem contraction_op_sq_zero (lambda : V →ₗ[R] R) (omega : ExteriorAlgebra R V) :
    (contractionOp lambda) ((contractionOp lambda) omega) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft
    (Q := (0 : QuadraticForm R V)) lambda omega

/-- **Theorem**: Global Contraction Annihilation Anti-Commutativity {ι_λ1, ι_λ2} = 0 in End(⋀ V). -/
theorem contraction_op_anticommute
    (lambda1 lambda2 : V →ₗ[R] R) (omega : ExteriorAlgebra R V) :
    (contractionOp lambda1) ((contractionOp lambda2) omega) +
    (contractionOp lambda2) ((contractionOp lambda1) omega) = 0 := by
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) lambda1
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) lambda2 omega) +
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) lambda2
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) lambda1 omega) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  simp


end InfoGeometry.Canonical.ExteriorContractionOperatorBridge
