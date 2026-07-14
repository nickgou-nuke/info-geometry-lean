import InfoGeometry.Canonical.SingularDecompositionSurrogate
import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Canonical.OperatorialCramerRao
import InfoGeometry.Canonical.ModularSpectralWedgeBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1

Chunk-1 translation of the state-first/type-III doctrine into repo-native Lean.

This file introduces no new ontology. It packages existing owners:

1. wedge-calibrated bounded relative modular split (CP-002 lane),
2. singular surrogate closure package (CP-003 lane),
3. operatorial Cramér-Rao lower bound (comparison-channel lane).
-/

namespace OperatorialCramerRaoStateFirstChunk1

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.OperatorialCramerRao

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
State-first witness bundle for Chunk-1:
modular calibration data plus operatorial Cramér-Rao channel response data.
-/
@[rep_depth transport]
structure StateFirstCRWitness
    (CIK : CertifiedInverseKernel H₂) where
  W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E
  calibrated :
    InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
      (E := E)
      (T := InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK)
      (W := W)
      (owned_epsilon := spectral_epsilon (E := E))
      (owned_P_D := CIK.spectralComplementaryProjector)
  comparison : H₂
  X : PerturbationChannel E
  Y : PerturbationChannel E
  unitResponse :
    InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
      (E := E) comparison X Y = 1
  yNontrivial : Y comparison ≠ 0

/--
Chunk-1 state-first package:

1. wedge-calibrated bounded relative modular representative splits across
   apex/active projectors,
2. singular surrogate commutator closure is available on the same calibrated lane,
3. operatorial Cramér-Rao lower bound holds on the comparison channels.
-/
@[rep_depth transport, capstone]
theorem stateFirst_modularSplit_singularClosure_operatorialCramerRao
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (τ : ℝ) :
    (InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
      (E := E) CIK τ
        =
      CIK.spectralComplementaryProjector
        * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
            (E := E) CIK τ
        * CIK.spectralComplementaryProjector
        +
      CIK.spectralProjector
        * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
            (E := E) CIK τ
        * CIK.spectralProjector
      ∧
      DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
        =
      DrazinSupercharge.commutator CIK.spectralProjector CIK.GammaG)
      ∧
    (1 /
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.Y S.Y
      ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.X S.X) := by
  refine ⟨?_, ?_⟩
  · exact
      InfoGeometry.Canonical.SingularDecompositionSurrogate.canonicalRelativeModularOperator_singular_surrogate_package_of_wedgeCalibrated
        (E := E)
        (CIK := CIK)
        (W := S.W)
        S.calibrated
        τ
  · exact
      inv_comparisonStateGeneratorMetric_self_le_of_unit_response
        (E := E)
        S.comparison
        S.X
        S.Y
        S.unitResponse
        S.yNontrivial

end Core

end OperatorialCramerRaoStateFirstChunk1
