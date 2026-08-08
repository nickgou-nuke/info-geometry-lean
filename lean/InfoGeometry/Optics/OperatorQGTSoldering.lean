import InfoGeometry.Optics.OperatorCausalSoldering
import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

/-!
# QGT operator soldering

The symmetric BKM channel and antisymmetric Berry channel are packaged as a
single operator-valued four-vector and soldered through the existing causal
operator reconstruction.  This owner introduces no second curvature or
matrix-algebra definition.
-/

noncomputable section

namespace InfoGeometry.Unified

open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Quantum.GeometricQuantumTensor
open SouriauOnsagerBKM

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

structure QGTFourVector (W : Type*) [AddCommGroup W] [Module ℂ W] where
  symmetricBKM : OperatorFourVector W
  antisymmetricBerry : OperatorFourVector W

def QGTFourVector.totalOperator (Q : QGTFourVector W) : OperatorFourVector W :=
  fun i => Q.symmetricBKM i + Complex.I • Q.antisymmetricBerry i

def QGTSoldering (Q : QGTFourVector W) : Module.End ℂ (Fin 2 → W) :=
  operatorSolderingAction Q.totalOperator

@[simp] theorem QGTFourVector.totalOperator_apply
    (Q : QGTFourVector W) (i : Fin 4) :
    Q.totalOperator i =
      Q.symmetricBKM i + Complex.I • Q.antisymmetricBerry i :=
  rfl

@[simp] theorem QGTSoldering_apply
    (Q : QGTFourVector W) (ψ : Fin 2 → W) (i : Fin 2) :
    QGTSoldering Q ψ i =
      ∑ j : Fin 2, operatorSoldering Q.totalOperator i j (ψ j) := by
  exact operatorSolderingAction_apply Q.totalOperator ψ i

theorem QGTSoldering_eq_operatorSolderingAction
    (Q : QGTFourVector W) :
    QGTSoldering Q = operatorSolderingAction Q.totalOperator :=
  rfl

end InfoGeometry.Unified
