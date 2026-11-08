/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BKMScalarGaugeQuotient
import InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration

/-!
# Mixed finite-family Gibbs CE Onsager response

The pairwise centered-BKM response of a finite CE observable family is
bilinear in two independent Fréchet-induced derivation directions. The
weighted pairwise sum is identified with the concrete Gibbs CE Onsager
dissipation and the real mixed log-partition Hessian at the weighted
aggregate observable.
-/

noncomputable section

namespace InfoGeometry.Canonical.CEBKMOnsagerGibbsFamilyBilinear

open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
open InfoGeometry.Canonical.CEBKMOnsagerSystem
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Optics.OperatorDerivationForms

/-- Expand the mixed centered-BKM response of a finite Gibbs CE family as
the response of the two coefficient-weighted readout sums. The two
Fréchet-induced directions are independent. -/
theorem finiteGibbsCEFamily_pairwiseBilinear_eq_aggregateBKM
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ)
    (D E : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H) :
    (∑ i, c i • ∑ j, c j •
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a j) (finiteCEFrechetDirection E))) =
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (∑ i, c i • finiteCEOperatorForm n (a i)
          (finiteCEFrechetDirection D))
        (∑ j, c j • finiteCEOperatorForm n (a j)
          (finiteCEFrechetDirection E)) := by
  let density := faithfulGibbsDensity H hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  let readoutD : Fin m → GibbsOperator n :=
    fun i => finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D)
  let readoutE : Fin m → GibbsOperator n :=
    fun i => finiteCEOperatorForm n (a i) (finiteCEFrechetDirection E)
  let quotientReadoutD : Fin m →
      GibbsOperator n ⧸ BKMScalarGaugeQuotient.scalarGauge n :=
    fun i => Submodule.Quotient.mk (readoutD i)
  let quotientReadoutE : Fin m →
      GibbsOperator n ⧸ BKMScalarGaugeQuotient.scalarGauge n :=
    fun i => Submodule.Quotient.mk (readoutE i)
  have hquotientSumD :
      (∑ i, c i • quotientReadoutD i) =
        (BKMScalarGaugeQuotient.scalarGauge n).mkQ
          (∑ i, c i • readoutD i) := by
    change (∑ i, c i •
        (BKMScalarGaugeQuotient.scalarGauge n).mkQ (readoutD i)) = _
    rw [map_sum]
    simp only [map_smul]
  have hquotientSumE :
      (∑ i, c i • quotientReadoutE i) =
        (BKMScalarGaugeQuotient.scalarGauge n).mkQ
          (∑ i, c i • readoutE i) := by
    change (∑ i, c i •
        (BKMScalarGaugeQuotient.scalarGauge n).mkQ (readoutE i)) = _
    rw [map_sum]
    simp only [map_smul]
  let B := quotientBKMForm density hpow
  have hbilinearExpansion :
      B (∑ i, c i • quotientReadoutD i)
          (∑ j, c j • quotientReadoutE j) =
        ∑ i, c i • ∑ j, c j •
          B (quotientReadoutD i) (quotientReadoutE j) := by
    have houter :
        B (∑ i, c i • quotientReadoutD i) =
          ∑ i, c i • B (quotientReadoutD i) := by
      simp only [map_sum, map_smul]
    have hinner (i : Fin m) :
        B (quotientReadoutD i) (∑ j, c j • quotientReadoutE j) =
          ∑ j, c j • B (quotientReadoutD i) (quotientReadoutE j) := by
      simp only [map_sum, map_smul]
    calc
      B (∑ i, c i • quotientReadoutD i)
          (∑ j, c j • quotientReadoutE j) =
        ∑ i, c i • B (quotientReadoutD i)
          (∑ j, c j • quotientReadoutE j) := by
            have h := congrArg
              (fun f : (GibbsOperator n ⧸
                BKMScalarGaugeQuotient.scalarGauge n) →ₗ[ℝ] ℝ =>
                  f (∑ j, c j • quotientReadoutE j)) houter
            simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using h
      _ = ∑ i, c i • ∑ j, c j •
            B (quotientReadoutD i) (quotientReadoutE j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hinner i]
  have hcovarianceExpansion :
      centeredBKMRealCovariance density hpow
          (∑ i, c i • readoutD i) (∑ j, c j • readoutE j) =
        ∑ i, c i • ∑ j, c j •
          centeredBKMRealCovariance density hpow
            (readoutD i) (readoutE j) := by
    calc
      centeredBKMRealCovariance density hpow
          (∑ i, c i • readoutD i) (∑ j, c j • readoutE j) =
        quotientBKMForm density hpow
          ((BKMScalarGaugeQuotient.scalarGauge n).mkQ
            (∑ i, c i • readoutD i))
          ((BKMScalarGaugeQuotient.scalarGauge n).mkQ
            (∑ j, c j • readoutE j)) := by
              change centeredBKMRealCovariance density hpow
                  (∑ i, c i • readoutD i) (∑ j, c j • readoutE j) =
                quotientBKMForm density hpow
                  (Submodule.Quotient.mk (∑ i, c i • readoutD i))
                  (Submodule.Quotient.mk (∑ j, c j • readoutE j))
              rw [BKMScalarGaugeQuotient.quotientBKMForm_mk]
      _ = B (∑ i, c i • quotientReadoutD i)
            (∑ j, c j • quotientReadoutE j) := by
              rw [← hquotientSumD, ← hquotientSumE]
      _ = ∑ i, c i • ∑ j, c j •
            B (quotientReadoutD i) (quotientReadoutE j) :=
              hbilinearExpansion
      _ = ∑ i, c i • ∑ j, c j •
            centeredBKMRealCovariance density hpow
              (readoutD i) (readoutE j) := by
              simp [quotientReadoutD, quotientReadoutE, B,
                BKMScalarGaugeQuotient.quotientBKMForm_mk]
  simpa [density, hpow, readoutD, readoutE] using
    hcovarianceExpansion.symm

/-- The mixed finite-family BKM response is the dissipative response of the
finite Gibbs CE Onsager system at the weighted aggregate observable, and
equals its real Gibbs log-partition Hessian. Self-adjointness is imposed on
the first aggregate readout, as required by the Hessian owner. -/
theorem finiteGibbsCEFamily_pairwiseBilinear_eq_aggregateOnsagerDissipation_hessian
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (Q : GibbsOperator n)
    (D E : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hD : IsSelfAdjoint
      (finiteCEOperatorForm n (∑ i, c i • a i)
        (finiteCEFrechetDirection D))) :
    (∑ i, c i • ∑ j, c j •
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a j) (finiteCEFrechetDirection E))) =
      (finiteGibbsCEOnsagerSystem H hH hZ (∑ i, c i • a i) Q).dissipative
        (finiteCEFrechetDirection D) (finiteCEFrechetDirection E) ∧
    (∑ i, c i • ∑ j, c j •
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a j) (finiteCEFrechetDirection E))) =
      (secondFDerivLogPartitionReadout H
        (finiteCEOperatorForm n (∑ i, c i • a i)
          (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (∑ i, c i • a i)
          (finiteCEFrechetDirection E))).re := by
  let b : GibbsOperator n := ∑ i, c i • a i
  let directionD := finiteCEFrechetDirection D
  let directionE := finiteCEFrechetDirection E
  let pairwiseResponse := ∑ i, c i • ∑ j, c j •
    centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ)
      (finiteCEOperatorForm n (a i) directionD)
      (finiteCEOperatorForm n (a j) directionE)
  have hpair := finiteGibbsCEFamily_pairwiseBilinear_eq_aggregateBKM
    H a c D E hH hZ
  have hreadoutD := finiteGibbsCEFamily_weightedReadout_eq a c D
  have hreadoutE := finiteGibbsCEFamily_weightedReadout_eq a c E
  have hdiss :
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n b directionD)
        (finiteCEOperatorForm n b directionE) =
      (finiteGibbsCEOnsagerSystem H hH hZ b Q).dissipative
        directionD directionE := by
    rw [← centeredCEBKMForm_apply]
    rfl
  have hmain : pairwiseResponse =
      (finiteGibbsCEOnsagerSystem H hH hZ b Q).dissipative
        directionD directionE := by
    calc
      pairwiseResponse =
          centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
            (continuous_faithfulGibbsDensity_rpow H hH hZ)
            (∑ i, c i • finiteCEOperatorForm n (a i) directionD)
            (∑ j, c j • finiteCEOperatorForm n (a j) directionE) := by
              simpa [pairwiseResponse, directionD, directionE] using hpair
      _ = centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
            (continuous_faithfulGibbsDensity_rpow H hH hZ)
            (finiteCEOperatorForm n b directionD)
            (finiteCEOperatorForm n b directionE) := by
              rw [show (∑ i, c i • finiteCEOperatorForm n (a i) directionD) =
                finiteCEOperatorForm n b directionD by
                  simpa [b, directionD] using hreadoutD]
              rw [show (∑ j, c j • finiteCEOperatorForm n (a j) directionE) =
                finiteCEOperatorForm n b directionE by
                  simpa [b, directionE] using hreadoutE]
      _ = (finiteGibbsCEOnsagerSystem H hH hZ b Q).dissipative
            directionD directionE := hdiss
  have hhess := finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian
    H b Q hH hZ D E (by simpa [b, directionD] using hD)
  constructor
  · simpa [pairwiseResponse, b, directionD, directionE] using hmain
  · calc
      pairwiseResponse =
          (finiteGibbsCEOnsagerSystem H hH hZ b Q).dissipative
            directionD directionE := hmain
      _ = (secondFDerivLogPartitionReadout H
          (finiteCEOperatorForm n b directionD)
          (finiteCEOperatorForm n b directionE)).re := hhess.symm

end InfoGeometry.Canonical.CEBKMOnsagerGibbsFamilyBilinear
