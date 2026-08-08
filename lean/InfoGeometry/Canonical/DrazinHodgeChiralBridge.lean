import InfoGeometry.Canonical.DrazinLightConeDictionary
import InfoGeometry.Canonical.DrazinPenroseDilationAlgebra
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.InverseKernelCartanCore
import InfoGeometry.Canonical.ChiralDrazinLightConeBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DrazinHodgeChiralBridge

Calibrated bridge from the Drazin/Moore--Penrose causal projector split to the
Hodge/Dirac chiral-arrow representation.

This file is not full Hodge theory.  It proves the finite algebraic dictionary:

* `P_SD = P_D`;
* `P_ASD = P₀`;
* `D⁺ = P₀ D P_D = u⁻(D)`;
* `D⁻ = P_D D P₀ = u⁺(D)`;
* `{D, Γ_S} = 0` implies `[D², Γ_S] = 0`.

The bridge keeps the surrogate Hamiltonian lane separate.  It identifies Hodge
chirality with the property spectral grading, builds the corresponding Drazin
`ProjectorSplit`, and reads the two Dirac arrows through the existing
`uPlus/uMinus` projector-arrow API.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.DrazinLightConeDictionary

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance drazinHodgeChiralBridgeNormedRing : NormedRing EndH :=
  inferInstance
noncomputable local instance drazinHodgeChiralBridgeNormedAlgebra : NormedAlgebra ℝ EndH :=
  inferInstance
local instance drazinHodgeChiralBridgeTopologicalRing : IsTopologicalRing EndH :=
  inferInstance
local instance drazinHodgeChiralBridgeSMulCommClass : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance drazinHodgeChiralBridgeIsScalarTower : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
A calibrated Hodge/Dirac carrier over the property inverse-kernel Drazin lane.

`dirac_odd` is the algebraic property `D ∈ 𝔭`; equivalently,
`D * Γ_S = -(Γ_S * D)`.
-/
@[rep_depth krein]
structure DrazinHodgeChiralBridge where
  CIK : CertifiedInverseKernel E
  Dirac : EndH
  dirac_odd : CIK.IsSpectralNonCompact Dirac

/-- Canonical Hodge/chiral bridge using the repo-owned Drazin supercharge. -/
@[rep_depth krein]
noncomputable def canonicalBridge
    (CIK : CertifiedInverseKernel E) : DrazinHodgeChiralBridge (E := E) where
  CIK := CIK
  Dirac := DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
  dirac_odd := by
    simpa [DrazinSupercharge.CertifiedInverseKernel.supercharge] using
      (DrazinSupercharge.CertifiedInverseKernel.supercharge_isSpectralNonCompact
        (CIK := CIK))

namespace DrazinHodgeChiralBridge

variable (B : DrazinHodgeChiralBridge (E := E))

/-- Certified Drazin regular/defect split as a generic projector split. -/
@[rep_depth krein]
noncomputable def drazinSplit : ProjectorSplit EndH where
  P := B.CIK.spectralProjector
  P0 := B.CIK.spectralComplementaryProjector
  P_idem := B.CIK.spectralProjector_idempotent
  P0_idem := B.CIK.spectralComplementaryProjector_idempotent
  P_add_P0 := B.CIK.spectralProjector_add_spectralComplementaryProjector
  P_mul_P0 := B.CIK.spectralProjector_mul_spectralComplementaryProjector
  P0_mul_P := B.CIK.spectralComplementaryProjector_mul_spectralProjector

/-- Hodge chirality calibrated to the property spectral grading. -/
@[rep_depth krein]
noncomputable def hodgeChirality : EndH :=
  B.CIK.GammaS

/--
Hodge star / chiral phase axis.

This is a calibrated alias for the Drazin spectral grading `Γ_S`.  It is not a
global metric Hodge-star construction.
-/
@[rep_depth krein]
noncomputable def hodgeStar : EndH :=
  B.hodgeChirality

/-- Calibration readback: the Hodge star/chiral axis is the spectral grading `Γ_S`. -/
@[rep_depth krein]
theorem hodgeStar_eq_GammaS :
    B.hodgeStar = B.CIK.GammaS := by
  rfl

/-- The calibrated Hodge star/chiral axis is involutive on this Drazin lane. -/
@[rep_depth krein]
theorem hodgeStar_sq_eq_one :
    B.hodgeStar * B.hodgeStar = (1 : EndH) := by
  unfold hodgeStar hodgeChirality
  exact B.CIK.GammaS_sq_eq_one

/-- Self-dual Hodge projector, defined from the calibrated chirality. -/
@[rep_depth krein]
noncomputable def hodgeSD : EndH :=
  (⅟ (2 : ℝ)) • ((ContinuousLinearMap.id ℝ E) + B.hodgeChirality)

/-- Anti-self-dual Hodge projector, defined from the calibrated chirality. -/
@[rep_depth krein]
noncomputable def hodgeASD : EndH :=
  (⅟ (2 : ℝ)) • ((ContinuousLinearMap.id ℝ E) - B.hodgeChirality)

/--
Hodge-side regular carrier.

This is only the regular Drazin carrier under the supplied chiral calibration;
it is not a full analytic exact/coexact Hodge decomposition.
-/
@[rep_depth krein]
noncomputable def hodgeRegularCarrier : EndH :=
  B.hodgeSD

/--
Hodge-side harmonic/defect remnant.

This names the Drazin defect sector `P₀ = 1 - P_D` in Hodge language.  It is
the part left behind by the regular inverse, not an automatically constructed
kernel of an analytic Laplacian.
-/
@[rep_depth krein]
noncomputable def hodgeHarmonicDefectRemnant : EndH :=
  B.hodgeASD

/-- Under the calibration `⋆χ = Γ_S`, the self-dual sector is the Drazin regular sector. -/
@[rep_depth krein]
theorem hodgeSD_eq_drazinRegular :
    B.hodgeSD = B.drazinSplit.P := by
  change B.hodgeSD = B.CIK.spectralProjector
  rw [hodgeSD, hodgeChirality, B.CIK.GammaS_eq_two_mul_spectralProjector_sub_one]
  calc
    (⅟ (2 : ℝ)) •
        ((ContinuousLinearMap.id ℝ E) + (2 * B.CIK.spectralProjector - 1))
        = (⅟ (2 : ℝ)) • (2 • B.CIK.spectralProjector) := by
            ext x
            simp
            module
    _ = B.CIK.spectralProjector := by
          ext x
          simp
          module

/-- Under the calibration `⋆χ = Γ_S`, the anti-self-dual sector is the Drazin defect sector. -/
@[rep_depth krein]
theorem hodgeASD_eq_drazinDefect :
    B.hodgeASD = B.drazinSplit.P0 := by
  change B.hodgeASD = B.CIK.spectralComplementaryProjector
  rw [hodgeASD, hodgeChirality, B.CIK.GammaS_eq_two_mul_spectralProjector_sub_one]
  unfold CertifiedInverseKernel.spectralComplementaryProjector
  unfold CertifiedInverseKernel.toInverseKernel'
  unfold InverseKernel.spectralComplementaryProjector
  calc
    (⅟ (2 : ℝ)) •
        ((ContinuousLinearMap.id ℝ E) - (2 * B.CIK.spectralProjector - 1))
        = (1 : EndH) - B.CIK.spectralProjector := by
            ext x
            simp
            module
    _ = 1 - B.CIK.spectralProjector := by
          rfl

/-- The Hodge-side regular carrier is exactly the Drazin regular projector `P_D`. -/
@[rep_depth krein]
theorem hodgeRegularCarrier_eq_drazinRegular :
    B.hodgeRegularCarrier = B.drazinSplit.P := by
  unfold hodgeRegularCarrier
  exact hodgeSD_eq_drazinRegular (B := B)

/-- The Hodge-side harmonic/defect remnant is exactly the Drazin defect projector `P₀`. -/
@[rep_depth krein]
theorem hodgeHarmonicDefectRemnant_eq_drazinDefect :
    B.hodgeHarmonicDefectRemnant = B.drazinSplit.P0 := by
  unfold hodgeHarmonicDefectRemnant
  exact hodgeASD_eq_drazinDefect (B := B)

/-- Readback: the harmonic/defect remnant is the property complementary projector. -/
@[rep_depth krein]
theorem hodgeHarmonicDefectRemnant_eq_spectralComplementaryProjector :
    B.hodgeHarmonicDefectRemnant = B.CIK.spectralComplementaryProjector := by
  exact hodgeHarmonicDefectRemnant_eq_drazinDefect (B := B)

/-- The `P_ASD D P_SD` Hodge/Dirac arrow. -/
@[rep_depth krein]
noncomputable def diracPlus : EndH :=
  B.hodgeASD * B.Dirac * B.hodgeSD

/-- The `P_SD D P_ASD` Hodge/Dirac arrow. -/
@[rep_depth krein]
noncomputable def diracMinus : EndH :=
  B.hodgeSD * B.Dirac * B.hodgeASD

/-- Repository convention: `D⁺ = P_ASD D P_SD = P₀ D P_D = u⁻(D)`. -/
@[rep_depth krein]
theorem diracPlus_eq_uMinus :
    B.diracPlus = B.drazinSplit.uMinus B.Dirac := by
  unfold diracPlus
  rw [hodgeASD_eq_drazinDefect (B := B), hodgeSD_eq_drazinRegular (B := B)]
  rfl

/-- Repository convention: `D⁻ = P_SD D P_ASD = P_D D P₀ = u⁺(D)`. -/
@[rep_depth krein]
theorem diracMinus_eq_uPlus :
    B.diracMinus = B.drazinSplit.uPlus B.Dirac := by
  unfold diracMinus
  rw [hodgeSD_eq_drazinRegular (B := B), hodgeASD_eq_drazinDefect (B := B)]
  rfl

/-- Same-arrow nilpotence for the `D⁺` channel. -/
@[rep_depth krein]
theorem diracPlus_mul_diracPlus_eq_zero :
    B.diracPlus * B.diracPlus = 0 := by
  rw [diracPlus_eq_uMinus (B := B)]
  exact B.drazinSplit.uMinus_mul_uMinus_eq_zero B.Dirac B.Dirac

/-- Same-arrow nilpotence for the `D⁻` channel. -/
@[rep_depth krein]
theorem diracMinus_mul_diracMinus_eq_zero :
    B.diracMinus * B.diracMinus = 0 := by
  rw [diracMinus_eq_uPlus (B := B)]
  exact B.drazinSplit.uPlus_mul_uPlus_eq_zero B.Dirac B.Dirac

/-- Positive/self-dual Hodge loop `D⁻D⁺`, supported on the regular sector. -/
@[rep_depth krein]
noncomputable def hodgeLapPlus : EndH :=
  B.diracMinus * B.diracPlus

/-- Negative/anti-self-dual Hodge loop `D⁺D⁻`, supported on the defect sector. -/
@[rep_depth krein]
noncomputable def hodgeLapMinus : EndH :=
  B.diracPlus * B.diracMinus

/-- Readback: `D⁻D⁺` is the Drazin mixed light-cone loop `u⁺(D)u⁻(D)`. -/
@[rep_depth krein]
theorem hodgeLapPlus_eq_uPlus_mul_uMinus :
    B.hodgeLapPlus = B.drazinSplit.uPlus B.Dirac * B.drazinSplit.uMinus B.Dirac := by
  unfold hodgeLapPlus
  rw [diracMinus_eq_uPlus (B := B), diracPlus_eq_uMinus (B := B)]

/-- Readback: `D⁺D⁻` is the Drazin mixed light-cone loop `u⁻(D)u⁺(D)`. -/
@[rep_depth krein]
theorem hodgeLapMinus_eq_uMinus_mul_uPlus :
    B.hodgeLapMinus = B.drazinSplit.uMinus B.Dirac * B.drazinSplit.uPlus B.Dirac := by
  unfold hodgeLapMinus
  rw [diracPlus_eq_uMinus (B := B), diracMinus_eq_uPlus (B := B)]

/-- The Drazin commutator with the regular projector is the chiral-arrow mismatch. -/
@[rep_depth krein]
theorem commutator_drazinRegular_Dirac_eq_diracMinus_sub_diracPlus :
    DrazinLightConeDictionary.commutator B.drazinSplit.P B.Dirac =
      B.diracMinus - B.diracPlus := by
  rw [diracMinus_eq_uPlus (B := B), diracPlus_eq_uMinus (B := B)]
  exact B.drazinSplit.commutator_P_eq_uPlus_sub_uMinus B.Dirac

/-! ## Moore--Penrose anomaly readbacks in the Hodge calibration -/

/--
Hodge-side domain projector.

This is a calibrated name for the Moore--Penrose left/domain projector.  The
bridge does not construct a new Hodge domain theory.
-/
@[rep_depth krein]
noncomputable def hodgeDomainProjector : EndH :=
  B.CIK.mpLeftProjector

/--
Hodge-side range projector.

This is a calibrated name for the Moore--Penrose right/range projector.  The
bridge does not construct a new Hodge range theory.
-/
@[rep_depth krein]
noncomputable def hodgeRangeProjector : EndH :=
  B.CIK.mpRightProjector

/-- Hodge-side left/domain anomaly `[P_SD, P_dom]`. -/
@[rep_depth krein]
noncomputable def hodgeLeftAnomaly : EndH :=
  DrazinLightConeDictionary.commutator B.hodgeSD B.hodgeDomainProjector

/-- Hodge-side right/range anomaly `[P_SD, P_ran]`. -/
@[rep_depth krein]
noncomputable def hodgeRightAnomaly : EndH :=
  DrazinLightConeDictionary.commutator B.hodgeSD B.hodgeRangeProjector

/-- Hodge-side anomaly supercharge `χ_R^H - χ_L^H`. -/
@[rep_depth krein]
noncomputable def hodgeSupercharge : EndH :=
  B.hodgeRightAnomaly - B.hodgeLeftAnomaly

/-- Drazin/MP anomaly supercharge `χ_R - χ_L`. -/
@[rep_depth krein]
noncomputable def drazinSupercharge : EndH :=
  B.CIK.rightAnomalyGenerator - B.CIK.leftAnomalyGenerator

/-- The calibrated Hodge domain projector is the Moore--Penrose left/domain projector. -/
@[rep_depth krein]
theorem hodgeDomainProjector_eq_mpLeftProjector :
    B.hodgeDomainProjector = B.CIK.mpLeftProjector := rfl

/-- The calibrated Hodge range projector is the Moore--Penrose right/range projector. -/
@[rep_depth krein]
theorem hodgeRangeProjector_eq_mpRightProjector :
    B.hodgeRangeProjector = B.CIK.mpRightProjector := rfl

/--
The Hodge left/domain anomaly is exactly the Drazin/Moore--Penrose left anomaly
under the calibration `P_SD = P_D`.
-/
@[rep_depth krein]
theorem hodgeLeftAnomaly_eq_drazinLeftAnomaly :
    B.hodgeLeftAnomaly = B.CIK.leftAnomalyGenerator := by
  unfold hodgeLeftAnomaly hodgeDomainProjector
  rw [hodgeSD_eq_drazinRegular (B := B)]
  rfl

/--
The Hodge right/range anomaly is exactly the Drazin/Moore--Penrose right anomaly
under the calibration `P_SD = P_D`.
-/
@[rep_depth krein]
theorem hodgeRightAnomaly_eq_drazinRightAnomaly :
    B.hodgeRightAnomaly = B.CIK.rightAnomalyGenerator := by
  unfold hodgeRightAnomaly hodgeRangeProjector
  rw [hodgeSD_eq_drazinRegular (B := B)]
  rfl

/--
Hodge-side anomaly mismatch readback:
`[P_SD, P_ran] - [P_SD, P_dom]` is the Drazin/MP chiral anomaly difference.
-/
@[rep_depth krein]
theorem hodgeAnomalyMismatch_eq_drazinAnomalyMismatch :
    B.hodgeRightAnomaly - B.hodgeLeftAnomaly =
      B.CIK.rightAnomalyGenerator - B.CIK.leftAnomalyGenerator := by
  rw [hodgeRightAnomaly_eq_drazinRightAnomaly (B := B),
    hodgeLeftAnomaly_eq_drazinLeftAnomaly (B := B)]

/-- The Hodge anomaly supercharge is the Drazin/MP anomaly supercharge. -/
@[rep_depth krein]
theorem hodgeSupercharge_eq_drazinSupercharge :
    B.hodgeSupercharge = B.drazinSupercharge := by
  unfold hodgeSupercharge drazinSupercharge
  exact hodgeAnomalyMismatch_eq_drazinAnomalyMismatch (B := B)

/--
The Hodge anomaly supercharge is the calibrated Drazin commutator
`[P_D, Γ_G]`.
-/
@[rep_depth krein]
theorem hodgeSupercharge_eq_commutator_drazinRegular_geometricGrading :
    B.hodgeSupercharge =
      B.CIK.drazinProjector * B.CIK.geometricCartanGenerator
        - B.CIK.geometricCartanGenerator * B.CIK.drazinProjector := by
  rw [hodgeSupercharge_eq_drazinSupercharge (B := B)]
  unfold drazinSupercharge
  exact B.CIK.drazinProjector_commutator_geometricCartanGenerator_eq_sub_anomalies.symm

/-- Readback into the existing split-`Cl(1,1)` `u⁻` light-cone channel. -/
@[rep_depth krein]
theorem diracPlus_eq_splitCl11_uMinus
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = B.CIK.GammaS) :
    B.diracPlus = Cl11PolarizedBasis.uMinus X B.Dirac := by
  calc
    B.diracPlus = B.drazinSplit.uMinus B.Dirac :=
      diracPlus_eq_uMinus (B := B)
    _ = B.CIK.spectralComplementaryProjector * B.Dirac * B.CIK.spectralProjector := by
      rfl
    _ = Cl11PolarizedBasis.uMinus X B.Dirac := by
      exact
        (ChiralDrazinLightConeBridge.uMinus_eq_spectralComplementaryProjector_mul_A_mul_spectralProjector
          (CIK := B.CIK) (X := X) (A := B.Dirac) hΓ).symm

/-- Readback into the existing split-`Cl(1,1)` `u⁺` light-cone channel. -/
@[rep_depth krein]
theorem diracMinus_eq_splitCl11_uPlus
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hΓ : X.eps = B.CIK.GammaS) :
    B.diracMinus = Cl11PolarizedBasis.uPlus X B.Dirac := by
  calc
    B.diracMinus = B.drazinSplit.uPlus B.Dirac :=
      diracMinus_eq_uPlus (B := B)
    _ = B.CIK.spectralProjector * B.Dirac * B.CIK.spectralComplementaryProjector := by
      rfl
    _ = Cl11PolarizedBasis.uPlus X B.Dirac := by
      exact
        (ChiralDrazinLightConeBridge.uPlus_eq_spectralProjector_mul_A_mul_spectralComplementaryProjector
          (CIK := B.CIK) (X := X) (A := B.Dirac) hΓ).symm

/-- Hodge/Dirac Laplacian generated by the odd Dirac operator. -/
@[rep_depth krein]
noncomputable def hodgeLaplacian : EndH :=
  B.Dirac * B.Dirac

/-- The calibrated Dirac operator anticommutes with the spectral grading. -/
@[rep_depth krein]
theorem dirac_mul_GammaS_eq_neg :
    B.Dirac * B.CIK.GammaS = -(B.CIK.GammaS * B.Dirac) := by
  exact (B.CIK.isSpectralNonCompact_iff_anticommute_GammaS).1 B.dirac_odd

/-- Algebraic closure: `DΓ = -ΓD` implies `D²Γ = ΓD²`. -/
@[rep_depth krein]
theorem laplacian_commutes_GammaS :
    B.hodgeLaplacian * B.CIK.GammaS =
      B.CIK.GammaS * B.hodgeLaplacian := by
  have hAnti : B.Dirac * B.CIK.GammaS = -(B.CIK.GammaS * B.Dirac) :=
    dirac_mul_GammaS_eq_neg (B := B)
  unfold hodgeLaplacian
  calc
    (B.Dirac * B.Dirac) * B.CIK.GammaS
        = B.Dirac * (B.Dirac * B.CIK.GammaS) := by
            simp [mul_assoc]
    _ = B.Dirac * (-(B.CIK.GammaS * B.Dirac)) := by
          rw [hAnti]
    _ = -(B.Dirac * (B.CIK.GammaS * B.Dirac)) := by
          simp
    _ = -((B.Dirac * B.CIK.GammaS) * B.Dirac) := by
          simp [mul_assoc]
    _ = -((-(B.CIK.GammaS * B.Dirac)) * B.Dirac) := by
          rw [hAnti]
    _ = (B.CIK.GammaS * B.Dirac) * B.Dirac := by
          simp
    _ = B.CIK.GammaS * (B.Dirac * B.Dirac) := by
          simp [mul_assoc]

/-- The Hodge/Dirac Laplacian is spectrally compact/even: `D² ∈ 𝔨`. -/
@[rep_depth krein]
theorem laplacianEven :
    B.CIK.IsSpectralCompact B.hodgeLaplacian := by
  rw [B.CIK.isSpectralCompact_iff_commute_GammaS]
  exact laplacian_commutes_GammaS (B := B)

/-! ## Modular-Hamiltonian surrogate connector -/

/--
If the calibrated Hodge/Dirac operator is the Drazin supercharge, then the
Hodge Laplacian `D²` is the uncompressed Drazin super-Hamiltonian.

This is the safe bridge into `SuperchargeModularHamiltonianBridge`: compression
and modular-energy scaling remain owned by that downstream module.
-/
@[rep_depth krein]
theorem hodgeLaplacian_eq_superHamiltonian_of_Dirac_eq_supercharge
    (hD : B.Dirac = DrazinSupercharge.CertifiedInverseKernel.supercharge B.CIK) :
    B.hodgeLaplacian =
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonian B.CIK := by
  unfold hodgeLaplacian
  rw [hD]
  rfl

/--
If `D = Q`, the regular compression of the Hodge Laplacian is exactly the
regular-restricted Drazin super-Hamiltonian used by the modular surrogate.
-/
@[rep_depth krein]
theorem regularCompressed_hodgeLaplacian_eq_regularRestrictedSuperHamiltonian_of_Dirac_eq_supercharge
    (hD : B.Dirac = DrazinSupercharge.CertifiedInverseKernel.supercharge B.CIK) :
    B.CIK.spectralProjector * B.hodgeLaplacian * B.CIK.spectralProjector =
      DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian B.CIK := by
  rw [hodgeLaplacian_eq_superHamiltonian_of_Dirac_eq_supercharge (B := B) hD]
  rfl

/--
Public Hodge-to-defect bridge spine.

This packages the calibrated chiral Hodge split and the Drazin regular/defect
split in the order the repo now treats as canonical:
1. Hodge chirality,
2. regular/defect projectors,
3. off-diagonal chiral arrows,
4. Laplacian evenness.
-/
@[rep_depth krein, capstone]
theorem hodge_defect_regular_spine :
    B.hodgeStar = B.CIK.GammaS
      ∧ B.hodgeRegularCarrier = B.drazinSplit.P
      ∧ B.hodgeHarmonicDefectRemnant = B.drazinSplit.P0
      ∧ B.diracPlus = B.drazinSplit.uMinus B.Dirac
      ∧ B.diracMinus = B.drazinSplit.uPlus B.Dirac
      ∧ B.diracPlus * B.diracPlus = 0
      ∧ B.diracMinus * B.diracMinus = 0
      ∧ B.hodgeLaplacian * B.CIK.GammaS = B.CIK.GammaS * B.hodgeLaplacian
      ∧ B.CIK.IsSpectralCompact B.hodgeLaplacian := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hodgeStar_eq_GammaS (B := B)
  · exact hodgeRegularCarrier_eq_drazinRegular (B := B)
  · exact hodgeHarmonicDefectRemnant_eq_drazinDefect (B := B)
  · exact diracPlus_eq_uMinus (B := B)
  · exact diracMinus_eq_uPlus (B := B)
  · exact diracPlus_mul_diracPlus_eq_zero (B := B)
  · exact diracMinus_mul_diracMinus_eq_zero (B := B)
  · exact laplacian_commutes_GammaS (B := B)
  · exact laplacianEven (B := B)

end DrazinHodgeChiralBridge

end Core

end InfoGeometry.Canonical
