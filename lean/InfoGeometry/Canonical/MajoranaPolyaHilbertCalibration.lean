import Mathlib
import InfoGeometry.Meta.CalibrationReexport
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

/-!
# InfoGeometry.Canonical.MajoranaPolyaHilbertCalibration

Canonical wrapper for the existing Majorana/Pólya--Hilbert socket.

This file adds no analytic content. It simply re-exports the socket's
existing calibration theorems under a canonical owner-facing namespace.
-/

noncomputable section

namespace InfoGeometry.Canonical.MajoranaPolyaHilbertCalibration

open InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

/-- Canonical re-export of the explicit-formula/Mellin socket theorem. -/
@[bridge_target_tag]
theorem mellinTransform_eq_explicitFormula
    {HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (T : MBKHeatTraceExplicitFormulaSocket
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    T.mellinTransform_eq_explicitFormula_law :=
  by reexport T.mellinTransform_eq_explicitFormula_certificate

/-- Canonical re-export of the zeta-zero / inverse-zeta pole socket theorem. -/
@[bridge_target_tag]
theorem zetaZeros_are_poles_of_inverseZeta
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.zetaZeros_are_poles_of_inverseZeta_law :=
  by reexport S.zetaZeros_are_poles_of_inverseZeta_certificate

/-- Canonical re-export of the Majorana/Witten inverse-zeta channel. -/
@[bridge_target_tag]
theorem wittenCharacter_inverseZeta
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.wittenCharacter_inverseZeta_law :=
  by reexport S.wittenCharacter_inverseZeta_certificate

/-- Canonical re-export of the spectral Pfaffian/completed-`Xi` channel. -/
@[bridge_target_tag]
theorem spectralPfaffian_completedXi
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.spectralPfaffian_completedXi_law :=
  by reexport S.spectralPfaffian_completedXi_certificate

/-- Canonical re-export of the completed-`Xi` zeros/spectral-zero theorem. -/
@[bridge_target_tag]
theorem completedXiZeros_are_spectralZeros
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.completedXiZeros_are_spectralZeros_law :=
  by reexport S.completedXiZeros_are_spectralZeros_certificate

/-- Canonical re-export of the Pfaffian/zeta identity socket theorem. -/
@[bridge_target_tag]
theorem pfaffian_zeta_identity
    {SpectralParameter PfaffianReadout ZetaReadout : Type*}
    (S : MajoranaPfaffianZetaSpectralSocket
      SpectralParameter PfaffianReadout ZetaReadout) :
    S.pfaffian_zeta_identity_law :=
  by reexport S.pfaffian_zeta_identity_certificate

/-- Canonical re-export of the completed-zeta factorization socket theorem. -/
@[bridge_target_tag]
theorem completedZeta_factorization
    {SpectralParameter ArchimedeanReadout FinitePrimeReadout
      CompletedZetaReadout : Type*}
    (A : ArchimedeanGammaFactorSocket
      SpectralParameter ArchimedeanReadout FinitePrimeReadout CompletedZetaReadout) :
    A.completedZeta_factorization_law :=
  by reexport A.completedZeta_factorization_certificate

/-- Canonical re-export of the completed-`Xi` zero/spectral-zero socket theorem. -/
@[bridge_target_tag]
theorem completedXiZero_iff_spectralZero
    {BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (S : CompletedXiSuperdeterminantIdentitySocket
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    S.completedXiZero_iff_spectralZero_law :=
  by reexport S.completedXiZero_iff_spectralZero_certificate

/-- Canonical re-export of the completed-`Xi` spectral reduction RH theorem. -/
@[bridge_target_tag]
theorem classicalRH_of_completedXi_spectral_reduction
    {SpectralOperator SpectralKernel CompletedXiReadout
      RenormalizedPfaffianReadout : Type*}
    (R : CompletedXiHilbertPolyaReduction
      SpectralOperator SpectralKernel CompletedXiReadout RenormalizedPfaffianReadout) :
    R.classicalRHStatement :=
  by reexport CompletedXiHilbertPolyaReduction.classicalRH_of_completedXi_spectral_reduction R

/-- Canonical re-export of the supplied Majorana spectral witness RH theorem. -/
@[bridge_target_tag]
theorem classicalRH_of_supplied_majorana_spectral_witness
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout : Type*}
    (B : MajoranaPolyaHilbertBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm) :
    B.classicalRHStatement :=
  by reexport MajoranaPolyaHilbertBridge.classicalRH_of_supplied_majorana_spectral_witness B

end InfoGeometry.Canonical.MajoranaPolyaHilbertCalibration
