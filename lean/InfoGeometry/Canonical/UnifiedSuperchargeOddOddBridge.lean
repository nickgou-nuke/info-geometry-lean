import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
import InfoGeometry.Canonical.SuperchargeOddOddDecomposition
import Mathlib

/-!
# InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge

Owner bridge from the repo-native `UnifiedSuperchargeAlgebra` Drazin lane to the
generic proof-carrying odd-odd decomposition interface.

This file strengthens the previous `SuperchargeOddOddDecomposition` shadow:

* the odd generators are no longer arbitrary fields;
* the translation and central lanes are derived from
  `UnifiedSuperchargeAlgebra`;
* the residual defect lane is definitionally the difference between the owner
  defect and central channels, and is proved to vanish on this owner slice.

So this is still a finite/operatorial shadow, but it is now tied to existing
repo owners rather than carried as free decomposition data.
-/

open scoped InnerProductSpace

namespace UnifiedSuperchargeOddOddBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
open InfoGeometry.Canonical.SuperchargeHoppingBridge
open InfoGeometry.Canonical.SuperchargeOddOddDecomposition

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

namespace UnifiedSuperchargePackage

variable (U : UnifiedSuperchargePackage (E := E))

/-- On the Drazin owner slice, the translation lane is the doubled kinetic part. -/
@[rep_depth transport]
noncomputable def ownerTranslationCandidate : EndH :=
  (2 : ℝ) • U.drazinTranslationCandidate

/--
The owner translation lane remains spectrally compact on the current Drazin
slice.

This is the direct owner witness showing that the doubled kinetic lane stays in
the even/spectral-compact sector inherited from `Q_D²`.
-/
@[rep_depth transport]
theorem ownerTranslationCandidate_isSpectralCompact :
    U.kernel.IsSpectralCompact (ownerTranslationCandidate U) := by
  rw [InfoGeometry.Canonical.CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS
    (CIK := U.kernel) (X := ownerTranslationCandidate U)]
  have hT :
      ownerTranslationCandidate U * U.kernel.GammaS
        =
      U.kernel.GammaS * ownerTranslationCandidate U := by
    have hBase :
        U.drazinTranslationCandidate * U.kernel.GammaS
          =
        U.kernel.GammaS * U.drazinTranslationCandidate := by
      exact
        (InfoGeometry.Canonical.CertifiedInverseKernel.isSpectralCompact_iff_commute_GammaS
          (CIK := U.kernel) (X := U.drazinTranslationCandidate)).1
          (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.drazinTranslationCandidate_isSpectralCompact
            (U := U))
    simp [ownerTranslationCandidate, hBase]
  exact hT

/-- On the Drazin owner slice, the central lane is the owned central candidate. -/
@[rep_depth transport]
noncomputable def ownerCentralCandidate : EndH :=
  U.drazinCentralCandidate

/--
Residual defect lane after separating the owned central candidate.

On the current owner slice, this residual vanishes because the direct Drazin
defect and KKT central channels already coincide.
-/
@[rep_depth transport]
noncomputable def ownerDefectResidual : EndH :=
  U.drazinDefectCandidate - U.drazinCentralCandidate

@[rep_depth transport]
theorem ownerDefectResidual_eq_zero :
    ownerDefectResidual U = 0 := by
  unfold ownerDefectResidual
  rw [U.drazinCentralCandidate_eq_defectCandidate]
  abel

/--
Repo-native odd-odd closure on the Drazin lane in three-channel form:

* translation/hopping channel,
* central/BPS channel,
* residual defect channel.

The residual channel is zero on this owner slice.
-/
@[capstone, rep_depth transport]
theorem oddOddBracket_eq_translation_plus_central_plus_defectResidual :
    oddOddBracket (U.QD) (U.QD) =
      ownerTranslationCandidate U
        + ownerCentralCandidate U
        + ownerDefectResidual U := by
  calc
    oddOddBracket (U.QD) (U.QD)
        = InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK (U.QD) (U.QD) := by
            simp [oddOddBracket, InfoGeometry.Canonical.DrazinSupercharge.anticommutatorK,
              InfoGeometry.Canonical.DrazinSupercharge.anticommutator]
    _ = (2 : ℝ) • U.drazinTranslationCandidate + U.drazinCentralCandidate := by
          exact U.projected_oddOdd_bracket_eq_two_smul_translation_plus_central
    _ = ownerTranslationCandidate U + ownerCentralCandidate U + ownerDefectResidual U := by
          rw [ownerDefectResidual_eq_zero (U := U)]
          simp [ownerTranslationCandidate, ownerCentralCandidate]

/-- Canonical odd-odd decomposition data derived from the unified owner lane. -/
@[rep_depth transport]
noncomputable def toOddOddDecompositionData :
    OddOddDecompositionData (E := H₂) where
  Qi := U.QD
  Qj := U.QD
  translationCandidate := ownerTranslationCandidate U
  centralCandidate := ownerCentralCandidate U
  defectCandidate := ownerDefectResidual U
  oddOdd_decomposition :=
    oddOddBracket_eq_translation_plus_central_plus_defectResidual (U := U)

@[rep_depth transport]
theorem toOddOddDecompositionData_defectCandidate_eq_zero :
    (toOddOddDecompositionData U).defectCandidate = 0 := by
  exact ownerDefectResidual_eq_zero (U := U)

/--
The derived owner data satisfies the generic odd-odd decomposition packet and
the central-lane entropy-vanishing law.
-/
@[rep_depth transport, capstone]
theorem toOddOddDecompositionData_packet :
    (oddOddBracket (toOddOddDecompositionData U).Qi (toOddOddDecompositionData U).Qj
        =
      (toOddOddDecompositionData U).translationCandidate
        + (toOddOddDecompositionData U).centralCandidate
        + (toOddOddDecompositionData U).defectCandidate)
      ∧
    (∀ ψ : H₂,
      ψ ∈ (toOddOddDecompositionData U).centralBPSCore →
        entropyProductionShadow (toOddOddDecompositionData U).centralCandidate ψ = 0) := by
  exact (toOddOddDecompositionData U).oddOdd_decomposition_packet

end UnifiedSuperchargePackage

end Core

end UnifiedSuperchargeOddOddBridge
