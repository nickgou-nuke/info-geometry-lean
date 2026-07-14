import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1
import InfoGeometry.Canonical.SingularDecompositionSurrogate
import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2

Chunk-2 translation of the state-first/type-III doctrine into repo-native Lean.

This file adds:

1. an explicit commutation interface on the certified spectral projector lane,
2. extraction of split/supercharge clauses from that interface,
3. apex-zero degeneration to the active block,
4. a state-first package combining apex-zero active-only split with the
   operatorial Cramér-Rao lower bound from Chunk-1.
-/

namespace OperatorialCramerRaoStateFirstChunk2

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.OperatorialCramerRao
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
Explicit commutation interface for Chunk-2:
the transport representative commutes with the certified spectral projector.
-/
@[rep_depth transport]
structure StateFirstCommutationInterface
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH) where
  commutes_with_spectralProjector : Commute CIK.spectralProjector R

/--
Wedge-calibrated canonical bounded relative modular representatives provide the
Chunk-2 commutation interface automatically.
-/
@[rep_depth transport]
theorem stateFirstCommutationInterface_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    StateFirstCommutationInterface
      (E := E) CIK
      (InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
        (E := E) CIK τ) := by
  refine ⟨?_⟩
  exact
    InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ |>.symm

/--
From one explicit commutation witness, recover the projector-compressed split
and the supercharge closure clause.
-/
@[rep_depth transport, capstone]
theorem modularSplit_and_supercharge_of_commutationInterface
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (I : StateFirstCommutationInterface (E := E) CIK R) :
    (R
      =
    CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector * R * CIK.spectralProjector)
      ∧
    (DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    DrazinSupercharge.commutator CIK.spectralProjector CIK.GammaG) := by
  exact
    ⟨
      (InfoGeometry.Canonical.SingularDecompositionSurrogate.singular_decomposition_surrogate_package_of_commute
        (E := E) (CIK := CIK) (R := R) I.commutes_with_spectralProjector).1,
      (InfoGeometry.Canonical.SingularDecompositionSurrogate.singular_decomposition_surrogate_package_of_commute
        (E := E) (CIK := CIK) (R := R) I.commutes_with_spectralProjector).2.2.2
    ⟩

/--
Apex-zero degeneration:
if the certified apex projector vanishes, the split collapses to the active
projector block.
-/
@[rep_depth transport, capstone]
theorem modularSplit_degenerates_to_active_of_apex_zero
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (I : StateFirstCommutationInterface (E := E) CIK R)
    (hApexZero : CIK.spectralComplementaryProjector = 0) :
    R = CIK.spectralProjector * R * CIK.spectralProjector := by
  have hSplit :
      R
        =
      CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
        +
      CIK.spectralProjector * R * CIK.spectralProjector :=
    (modularSplit_and_supercharge_of_commutationInterface
      (E := E) (CIK := CIK) (R := R) I).1
  rw [hApexZero] at hSplit
  simpa using hSplit

/--
Chunk-2 capstone package:
under apex-zero, the canonical bounded relative modular representative is
active-only; the operatorial Cramér-Rao lower bound from Chunk-1 is preserved.
-/
@[rep_depth transport, capstone]
theorem stateFirst_apexZero_activeOnly_operatorialCramerRao
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (hApexZero : CIK.spectralComplementaryProjector = 0)
    (τ : ℝ) :
    (InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
      (E := E) CIK τ
        =
      CIK.spectralProjector
        * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
            (E := E) CIK τ
        * CIK.spectralProjector)
      ∧
    (1 /
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.Y S.Y
      ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.X S.X) := by
  refine ⟨?_, ?_⟩
  · have hIface :
        StateFirstCommutationInterface
          (E := E) CIK
          (InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
            (E := E) CIK τ) :=
      stateFirstCommutationInterface_of_wedgeCalibrated
        (E := E) (CIK := CIK) (W := S.W) S.calibrated τ
    exact
      modularSplit_degenerates_to_active_of_apex_zero
        (E := E)
        (CIK := CIK)
        (R := InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
          (E := E) CIK τ)
        hIface
        hApexZero
  · exact
      (stateFirst_modularSplit_singularClosure_operatorialCramerRao
        (E := E) (CIK := CIK) (S := S) τ).2

end Core

end OperatorialCramerRaoStateFirstChunk2
