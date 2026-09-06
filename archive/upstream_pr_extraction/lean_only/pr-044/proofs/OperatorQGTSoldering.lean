import Mathlib
import InfoGeometry.Optics.OperatorCausalSoldering
import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

noncomputable section

namespace InfoGeometry.Unified

open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Quantum.GeometricQuantumTensor
open SouriauOnsagerBKM

variable {Point Tangent W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The total QGT operator four-vector decomposes into a symmetric information
metric channel and an antisymmetric Berry curvature channel. -/
structure QGTFourVector (W : Type*) [AddCommGroup W] [Module ℂ W] where
  symmetricBKM : OperatorFourVector W
  antisymmetricBerry : OperatorFourVector W

/-- The total operator-valued geometric tensor is the complex sum of the
symmetric and antisymmetric channels. -/
def QGTFourVector.totalOperator (Q : QGTFourVector W) : OperatorFourVector W :=
  fun i => Q.symmetricBKM i + Complex.I • Q.antisymmetricBerry i

/-- Soldering the QGT into the doubled carrier using the verified operator soldering map. -/
def QGTSoldering (Q : QGTFourVector W) : Module.End ℂ (Fin 2 → W) :=
  operatorSolderingAction (Q.totalOperator)

@[simp] theorem QGTFourVector.totalOperator_apply
    (Q : QGTFourVector W) (i : Fin 4) :
    Q.totalOperator i =
      Q.symmetricBKM i + Complex.I • Q.antisymmetricBerry i :=
  rfl

/-- The doubled-carrier action of the soldered QGT channel. -/
@[simp] theorem QGTSoldering_apply
    (Q : QGTFourVector W) (ψ : Fin 2 → W) (i : Fin 2) :
    QGTSoldering Q ψ i =
      ∑ j : Fin 2,
        operatorSoldering Q.totalOperator i j (ψ j) := by
  exact operatorSolderingAction_apply Q.totalOperator ψ i

/-- The QGT channel is reconstructed through the verified operator soldering. -/
theorem QGTSoldering_eq_operatorSolderingAction
    (Q : QGTFourVector W) :
    QGTSoldering Q = operatorSolderingAction Q.totalOperator :=
  rfl

end InfoGeometry.Unified
