/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FockOccupationCarrierEquiv
import InfoGeometry.Twistor.RealSupertwistorOperators

/-!
# Finite Clifford–Fock stages on the common CAR–CCR supertwistor carrier

The finite split-Clifford matrix stage acts on the exterior-Fock carrier through
the repository's existing carrier equivalence. Tensoring that action with the
identity on polynomial wavefunctions places it on the existing common
supertwistor carrier, where the bosonic CCR and fermionic CAR coexist and
commute across tensor factors.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordFockSuperTwistorBridge

open InfoGeometry.Twistor.RealSupertwistor
open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Clifford.FockOccupationCarrierEquiv
open InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
open scoped TensorProduct
attribute [local instance] InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockNormedAddCommGroup
  InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockInnerProductSpace

/-- The existing finite Clifford matrix stage represented on the common
polynomial/exterior-Fock supertwistor carrier. -/
def cliffordStageRep (n : ℕ) :
    ClStage n →ₐ[ℝ] SuperOperator (Fin n) (Fin n → ℝ) :=
  (fermionLift (Fin n) (Fin n → ℝ)).comp
    (exteriorFockCliffordOperatorEquiv n).symm.toAlgHom

/-- The finite-stage exterior creation operator, represented on the common
supertwistor carrier. -/
def stageCreation (n : ℕ) (i : Fin n) : SuperOperator (Fin n) (Fin n → ℝ) :=
  cliffordStageRep n
    (exteriorFockCliffordOperatorEquiv n
      (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM n i).toLinearMap)

/-- The finite-stage exterior contraction operator, represented on the common
supertwistor carrier. -/
def stageContraction (n : ℕ) (i : Fin n) : SuperOperator (Fin n) (Fin n → ℝ) :=
  cliffordStageRep n
    (exteriorFockCliffordOperatorEquiv n
      (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM n i).toLinearMap)

/-- The finite Clifford-stage creation and contraction operators satisfy CAR
after both are represented on the common bosonic/fermionic carrier. -/
theorem stageCreation_contraction_CAR (n : ℕ) (i : Fin n) :
    stageContraction n i * stageCreation n i +
      stageCreation n i * stageContraction n i = 1 := by
  have h := congrArg (cliffordStageRep n)
    (exteriorFockClifford_CAR n i)
  change stageContraction n i * stageCreation n i +
      stageCreation n i * stageContraction n i = 1
  simpa [stageContraction, stageCreation, cliffordStageRep,
    AlgEquiv.symm_apply_apply] using h

/-- Every represented finite Clifford-stage operator commutes with the
polynomial CCR algebra acting on the other tensor factor. -/
theorem boson_commutes_with_cliffordStageRep (n : ℕ)
    (b : Operator (Fin n)) (x : ClStage n) :
    bosonLift (Fin n) (Fin n → ℝ) b * cliffordStageRep n x =
      cliffordStageRep n x * bosonLift (Fin n) (Fin n → ℝ) b :=
  boson_fermion_commute (ι := Fin n) (E := Fin n → ℝ) b
    ((exteriorFockCliffordOperatorEquiv n).symm x)

/-- The same tensor-factor commutation holds for the finite-stage CAR
generators themselves. -/
theorem boson_commutes_with_stageCreation (n : ℕ) (b : Operator (Fin n))
    (i : Fin n) :
    bosonLift (Fin n) (Fin n → ℝ) b * stageCreation n i =
      stageCreation n i * bosonLift (Fin n) (Fin n → ℝ) b := by
  exact boson_commutes_with_cliffordStageRep n b _

end InfoGeometry.Canonical.CliffordFockSuperTwistorBridge

end
