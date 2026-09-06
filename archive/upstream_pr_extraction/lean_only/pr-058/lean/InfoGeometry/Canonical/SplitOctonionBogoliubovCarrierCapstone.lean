import InfoGeometry.Canonical.SplitOctonionBogoliubovCarrierBridge

/-!
# Continuous carrier capstone for the split-octonion/Bogoliubov bridge

The split-octonion source has no canonical normed-space instance in this
repository.  Thus continuity cannot be inferred from a linear carrier
equivalence.  This owner records the minimal explicit continuous witness and
proves the resulting generator and finite-flow transport laws.
-/

noncomputable section

namespace InfoGeometry.Canonical

open SplitOctonion
open BogoliubovVielbein
open InfoGeometry.Krein

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

theorem quaternionicTransportedHyperbolicAxisOperator_eq_leftRegular_transport
    (g : Quaternion ℝ) :
    quaternionicTransportedHyperbolicAxisOperator g =
      (splitOctonionQuaternionicCarrierEquiv.toLinearMap.comp
        (leftRegular (J_g g))).comp
        splitOctonionQuaternionicCarrierEquiv.symm.toLinearMap := by
  rfl

theorem canonicalQuaternionicGenerator_eq_leftRegular_transport
    (g : Quaternion ℝ) :
    (canonicalQuaternionicBogoliubovVielbein g).connectionGenerator.toLinearMap =
      (splitOctonionQuaternionicCarrierEquiv.toLinearMap.comp
        (leftRegular (J_g g))).comp
        splitOctonionQuaternionicCarrierEquiv.symm.toLinearMap := by
  rw [canonicalQuaternionicBogoliubovVielbein_generator]
  exact quaternionicTransportedHyperbolicAxisOperator_eq_leftRegular_transport g

structure ContinuousCarrierDatum
    (g : Quaternion ℝ) (V : BogoliubovVielbeinBundle (E := E)) where
  linearDatum : SplitOctonionBogoliubovCarrierDatum (E := E) g V
  continuousGenerator : EndH
  continuousGenerator_toLinearMap :
    continuousGenerator.toLinearMap = linearDatum.transportedGenerator

namespace ContinuousCarrierDatum

theorem continuousGenerator_eq_connectionGenerator
    (D : ContinuousCarrierDatum (E := E) g V) :
    D.continuousGenerator = V.connectionGenerator := by
  apply ContinuousLinearMap.ext
  intro x
  have h₁ := LinearMap.congr_fun D.continuousGenerator_toLinearMap x
  have h₂ := LinearMap.congr_fun
    D.linearDatum.transportedGenerator_eq_connectionGenerator x
  simpa using h₁.trans h₂

noncomputable def transportedFlowCLM
    (D : ContinuousCarrierDatum (E := E) g V) (η : ℝ) : EndH :=
  (Real.cosh η) • ContinuousLinearMap.id ℝ H₂ +
    (Real.sinh η) • D.continuousGenerator

noncomputable def bogoliubovGeneratorFlowCLM
    (V : BogoliubovVielbeinBundle (E := E)) (η : ℝ) : EndH :=
  (Real.cosh η) • ContinuousLinearMap.id ℝ H₂ +
    (Real.sinh η) • V.connectionGenerator

theorem transportedFlowCLM_eq_bogoliubovGeneratorFlowCLM
    (D : ContinuousCarrierDatum (E := E) g V) (η : ℝ) :
    D.transportedFlowCLM η = bogoliubovGeneratorFlowCLM V η := by
  simp [transportedFlowCLM, bogoliubovGeneratorFlowCLM,
    D.continuousGenerator_eq_connectionGenerator]

omit [CompleteSpace E] in
theorem transportedFlowCLM_toLinearMap
    (D : ContinuousCarrierDatum (E := E) g V) (η : ℝ) :
    (D.transportedFlowCLM η).toLinearMap =
      (Real.cosh η) • LinearMap.id +
        (Real.sinh η) • D.linearDatum.transportedGenerator := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun D.continuousGenerator_toLinearMap x
  simp [transportedFlowCLM]
  exact congrArg (fun y => Real.sinh η • y) h

end ContinuousCarrierDatum

end InfoGeometry.Canonical
