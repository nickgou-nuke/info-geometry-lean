import InfoGeometry.Canonical.GlobalChiralDecomposition
import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SingularDecompositionSurrogate

CP-003 canopy surface in repo-native language.

This file does not introduce new ontology or existential KAN factors.
It packages existing owner theorems into a single surrogate-closure interface.
-/

namespace InfoGeometry.Canonical.SingularDecompositionSurrogate

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.GlobalChiralDecomposition
open InfoGeometry.Canonical.RelativeModularScaleShapeSplit
open InfoGeometry.Canonical.DrazinPenroseDilationKKT
open InfoGeometry.Canonical.DrazinSupercharge

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
CP-003 surrogate clause (active/apex lane):
projector-compressed decomposition under commutation with `P_D`.
-/
@[rep_depth transport]
theorem global_active_apex_decomposition
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (hComm : Commute CIK.spectralProjector R) :
    R
      =
    CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector * R * CIK.spectralProjector := by
  exact
    InfoGeometry.Canonical.GlobalChiralDecomposition.global_active_apex_decomposition
      (E := E) (CIK := CIK) (R := R) hComm

/--
CP-003 surrogate clause (range/domain lane):
`Γ_G = P_R - P_L`.
-/
@[rep_depth krein]
theorem chiral_range_domain_decomposition
    (K : DPDKKT H₂) :
    K.GammaG = K.P_R - K.P_L := by
  exact
    InfoGeometry.Canonical.GlobalChiralDecomposition.chiral_range_domain_decomposition
      (E := E) K

/--
CP-003 surrogate clause (anomaly closure lane):
`[P_D, Γ_G] = χ_R - χ_L`.
-/
@[rep_depth krein]
theorem singular_polar_surrogate_closure
    (K : DPDKKT H₂) :
    DrazinPenroseDilationKKT.commutator K.P_D K.GammaG
      =
    K.rightSupercharge - K.leftSupercharge := by
  exact
    InfoGeometry.Canonical.GlobalChiralDecomposition.singular_polar_surrogate_closure
      (E := E) K

/--
CP-002/CP-003 bridge clause:
one commutation witness yields both split surfaces
(nested projector form and projector-compressed form).
-/
@[rep_depth transport]
theorem relativeModular_scaleShapeSplit_bridge_of_commute
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (hComm : Commute CIK.spectralProjector R) :
    (R =
      CIK.spectralComplementaryProjector * (R * CIK.spectralComplementaryProjector)
        + CIK.spectralProjector * (R * CIK.spectralProjector))
      ∧
    (R =
      CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
        + CIK.spectralProjector * R * CIK.spectralProjector) := by
  exact cp002_cp003_bridge_of_commute (E := E) (CIK := CIK) (R := R) hComm

/--
CP-003 capstone package:
surrogate decomposition/closure bundle in current owner vocabulary.
-/
@[rep_depth transport, capstone]
theorem singular_decomposition_surrogate_package_of_commute
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (hComm : Commute CIK.spectralProjector R) :
    R
      =
    CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector * R * CIK.spectralProjector
      ∧
    CIK.mpRangeProjector - CIK.metricProjector = (2 : ℝ) • CIK.dilationGap
      ∧
    CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector
      =
    ((2 : ℝ)⁻¹) • (CIK.rightChiralAnomaly - CIK.chiralAnomaly)
      ∧
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    DrazinSupercharge.commutator CIK.spectralProjector CIK.GammaG := by
  rcases
      InfoGeometry.Canonical.GlobalChiralDecomposition.singularPolarKAN_replacement_of_commute
        (E := E) (CIK := CIK) (R := R) hComm
    with ⟨hSplit, hRangeDomain, hCommutator⟩
  refine ⟨hSplit, hRangeDomain, hCommutator, ?_⟩
  exact
    InfoGeometry.Canonical.GlobalChiralDecomposition.supergraded_supercharge_closure
      (E := E) CIK

/--
Wedge-calibrated specialization of the CP-003 surrogate package:
the canonical bounded relative modular representative splits across
apex/active Drazin blocks, together with the supercharge commutator closure.
-/
@[rep_depth transport, capstone]
theorem canonicalRelativeModularOperator_singular_surrogate_package_of_wedgeCalibrated
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
    canonicalRelativeModularOperator (E := E) CIK τ
      =
    CIK.spectralComplementaryProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector
      ∧
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    DrazinSupercharge.commutator CIK.spectralProjector CIK.GammaG := by
  refine ⟨?_, ?_⟩
  · exact
      canonicalRelativeModularOperator_scaleShapeSplit_of_wedgeCalibrated
        (E := E) (CIK := CIK) (W := W) C τ
  · exact
      InfoGeometry.Canonical.GlobalChiralDecomposition.supergraded_supercharge_closure
        (E := E) CIK

/--
Wedge-calibrated mixed-block vanishing for the canonical bounded relative modular
representative on the Drazin active/apex split.
-/
@[rep_depth transport]
theorem canonicalRelativeModularOperator_mixed_blocks_zero_of_wedgeCalibrated
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
    CIK.spectralComplementaryProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector
      = 0
      ∧
    CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralComplementaryProjector
      = 0 := by
  have hComm :
      Commute
        (canonicalRelativeModularOperator (E := E) CIK τ)
        CIK.spectralProjector :=
    canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ
  exact
    relativeModular_block_diagonal
      (E := E) (CIK := CIK)
      (R := canonicalRelativeModularOperator (E := E) CIK τ)
      hComm.symm

/--
Wedge-calibrated support identities for the apex block and active block of the
canonical bounded relative modular representative.
-/
@[rep_depth transport]
theorem canonicalRelativeModularOperator_block_support_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (_C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    CIK.spectralComplementaryProjector
      * (CIK.spectralComplementaryProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralComplementaryProjector)
      =
    CIK.spectralComplementaryProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralComplementaryProjector
      ∧
    (CIK.spectralComplementaryProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralComplementaryProjector)
      * CIK.spectralComplementaryProjector
      =
    CIK.spectralComplementaryProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralComplementaryProjector
      ∧
    CIK.spectralProjector
      * (CIK.spectralProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralProjector)
      =
    CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector
      ∧
    (CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector)
      * CIK.spectralProjector
      =
    CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      CIK.spectralComplementaryProjector
          * (CIK.spectralComplementaryProjector
              * canonicalRelativeModularOperator (E := E) CIK τ
              * CIK.spectralComplementaryProjector)
          =
        (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector)
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralComplementaryProjector := by
            simp [mul_assoc]
      _ =
        CIK.spectralComplementaryProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralComplementaryProjector := by
            simp [CIK.spectralComplementaryProjector_idempotent]
  · calc
      (CIK.spectralComplementaryProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralComplementaryProjector)
          * CIK.spectralComplementaryProjector
          =
        CIK.spectralComplementaryProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector) := by
            simp [mul_assoc]
      _ =
        CIK.spectralComplementaryProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralComplementaryProjector := by
            simp [CIK.spectralComplementaryProjector_idempotent]
  · calc
      CIK.spectralProjector
          * (CIK.spectralProjector
              * (canonicalRelativeModularOperator (E := E) CIK τ * CIK.spectralProjector))
          =
        (CIK.spectralProjector * CIK.spectralProjector)
          * (canonicalRelativeModularOperator (E := E) CIK τ * CIK.spectralProjector) := by
            rw [← mul_assoc]
      _ =
        CIK.spectralProjector
          * (canonicalRelativeModularOperator (E := E) CIK τ * CIK.spectralProjector) := by
            rw [CIK.spectralProjector_idempotent]
  · calc
      (CIK.spectralProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralProjector)
          * CIK.spectralProjector
          =
        CIK.spectralProjector
          * (canonicalRelativeModularOperator (E := E) CIK τ
              * (CIK.spectralProjector * CIK.spectralProjector)) := by
            simp [mul_assoc]
      _ =
        CIK.spectralProjector
          * (canonicalRelativeModularOperator (E := E) CIK τ * CIK.spectralProjector) := by
            simp [CIK.spectralProjector_idempotent]

/--
Wedge-calibrated active/apex stability package for the canonical bounded relative
modular representative: mixed blocks vanish and both diagonal blocks are
projector-supported on their respective lanes.
-/
@[rep_depth transport, capstone]
theorem canonicalRelativeModularOperator_activeApex_stability_of_wedgeCalibrated
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
    (CIK.spectralComplementaryProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector = 0)
      ∧
    (CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralComplementaryProjector = 0)
      ∧
    (CIK.spectralComplementaryProjector
      * (CIK.spectralComplementaryProjector
          * canonicalRelativeModularOperator (E := E) CIK τ
          * CIK.spectralComplementaryProjector)
      =
    CIK.spectralComplementaryProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralComplementaryProjector)
      ∧
    ((CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector)
      * CIK.spectralProjector
      =
    CIK.spectralProjector
      * canonicalRelativeModularOperator (E := E) CIK τ
      * CIK.spectralProjector) := by
  have hMixed :=
    canonicalRelativeModularOperator_mixed_blocks_zero_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ
  have hSupport :=
    canonicalRelativeModularOperator_block_support_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ
  refine ⟨hMixed.1, hMixed.2, hSupport.1, ?_⟩
  exact hSupport.2.2.2

end Core

end InfoGeometry.Canonical.SingularDecompositionSurrogate
