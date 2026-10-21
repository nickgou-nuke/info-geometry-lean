/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
import InfoGeometry.Canonical.BKMScalarGaugeQuotient
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge

/-!
# Finite Gibbs Onsager system on an `NOperatorForm` family

The carrier is a finite product of derivation directions, one for each
component of an actual CE family encoded by `ofCEFamily`. Dissipation is the
centered BKM form on the weighted sum of component readouts. The reversible
form is the weighted sum of the fixed-probe BKM readouts of the component CE
curvatures; no curvature-of-a-sum identity is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily

open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
open InfoGeometry.Canonical.CEBKMOnsagerSystem
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Thermo.OnsagerClosure

abbrev FamilyCarrier (m n : ℕ) :=
  Fin m → Carrier n

/-- The actual `NOperatorForm` family associated to finite Gibbs observables.
Its components are degree-zero CE cochains, not unrestricted pointwise
functions. -/
def finiteGibbsCEFamilyNOperatorForm {m n : ℕ}
    (a : Fin m → GibbsOperator n) :
    NOperatorForm m (Point := Unit)
      (Tangent := Carrier n) (Value := GibbsOperator n) :=
  ofCEFamily (realDerivationsLane (GibbsOperator n)) m
    (fun i => exteriorDerivativeZero
      (realDerivationsLane (GibbsOperator n)) (a i))

/-- Extract the `i`th genuine linear form from the encoded CE family. -/
def finiteGibbsCEFamilyComponentForm {m n : ℕ}
    (a : Fin m → GibbsOperator n) (i : Fin m) :
    Op1Form ℝ (Carrier n) (GibbsOperator n) :=
  component (realDerivationsLane (GibbsOperator n)) m
    (fun j => exteriorDerivativeZero
      (realDerivationsLane (GibbsOperator n)) (a j)) i

theorem finiteGibbsCEFamilyNOperatorComponent_eq_firstFrechetJet
    {m n : ℕ} (a : Fin m → GibbsOperator n)
    (D : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n))
    (x : GibbsOperator n) (i : Fin m) :
    finiteGibbsCEFamilyNOperatorForm a i ()
        (finiteCEFrechetDirection (D i)) =
      finiteGibbsCEFamilyComponentForm a i
        (finiteCEFrechetDirection (D i)) ∧
    finiteGibbsCEFamilyComponentForm a i
        (finiteCEFrechetDirection (D i)) =
      operatorFrechetJet 1 (D i : GibbsOperator n → GibbsOperator n) x
        (fun _ : Fin 1 => a i) := by
  have hcomponent :
      finiteGibbsCEFamilyNOperatorForm a i ()
          (finiteCEFrechetDirection (D i)) =
        finiteGibbsCEFamilyComponentForm a i
          (finiteCEFrechetDirection (D i)) := by
    change ofCEFamily (realDerivationsLane (GibbsOperator n)) m
        (fun j => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a j)) i ()
        (finiteCEFrechetDirection (D i)) =
      component (realDerivationsLane (GibbsOperator n)) m
        (fun j => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a j)) i
        (finiteCEFrechetDirection (D i))
    rw [component_apply]
    rfl
  refine ⟨hcomponent, ?_⟩
  calc
    finiteGibbsCEFamilyComponentForm a i
        (finiteCEFrechetDirection (D i)) =
      finiteGibbsCEFamilyNOperatorForm a i ()
        (finiteCEFrechetDirection (D i)) := hcomponent.symm
    _ = operatorFrechetJet 1
        (D i : GibbsOperator n → GibbsOperator n) x
        (fun _ : Fin 1 => a i) := by
          simpa [finiteGibbsCEFamilyNOperatorForm] using
            finiteGibbsCEFamily_component_eq_firstFrechetJet a (D i) x i

@[simp] theorem finiteGibbsCEFamilyComponentForm_apply
    {m n : ℕ} (a : Fin m → GibbsOperator n) (i : Fin m)
    (x : Carrier n) :
    finiteGibbsCEFamilyComponentForm a i x =
      finiteCEOperatorForm n (a i) x := by
  simp [finiteGibbsCEFamilyComponentForm, finiteCEOperatorForm,
    component_apply]

/-- Componentwise Fréchet derivations mapped into the real CE direction
carrier. -/
def finiteCEFrechetFamilyDirection {m n : ℕ}
    (D : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n)) :
    FamilyCarrier m n :=
  fun i => finiteCEFrechetDirection (D i)

/-- The weighted family readout is a genuine linear map on the product
direction carrier, assembled from the extracted `Op1Form` components. -/
def finiteGibbsCEFamilyNOperatorReadoutLinear {m n : ℕ}
    (a : Fin m → GibbsOperator n) (c : Fin m → ℝ) :
    FamilyCarrier m n →ₗ[ℝ] GibbsOperator n :=
  ∑ i, c i •
    (finiteGibbsCEFamilyComponentForm a i).comp (LinearMap.proj i)

@[simp] theorem finiteGibbsCEFamilyNOperatorReadoutLinear_apply
    {m n : ℕ} (a : Fin m → GibbsOperator n) (c : Fin m → ℝ)
    (x : FamilyCarrier m n) :
    finiteGibbsCEFamilyNOperatorReadoutLinear a c x =
      ∑ i, c i • finiteGibbsCEFamilyComponentForm a i (x i) := by
  simp [finiteGibbsCEFamilyNOperatorReadoutLinear]

/-- Pull the finite centered BKM covariance back along the weighted
`NOperatorForm` family readout. -/
def finiteCEFamilyNOperatorDissipativeForm {m n : ℕ}
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) : LinearMap.BilinForm ℝ (FamilyCarrier m n) :=
  (D.bkmRealBilinForm hpow).compl₁₂
    ((centeringLinearMap D hpow).comp
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c))
    ((centeringLinearMap D hpow).comp
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c))

@[simp] theorem finiteCEFamilyNOperatorDissipativeForm_apply
    {m n : ℕ} (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (x y : FamilyCarrier m n) :
    finiteCEFamilyNOperatorDissipativeForm D hpow a c x y =
      centeredBKMRealCovariance D hpow
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c x)
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c y) := by
  simp only [finiteCEFamilyNOperatorDissipativeForm,
    LinearMap.compl₁₂_apply, LinearMap.comp_apply,
    BKMScalarGaugeQuotient.centeringLinearMap_apply,
    centeredBKMRealCovariance]

/-- Sum the actual component CE-curvature probes on the product carrier. -/
def finiteCEFamilyNOperatorCurvatureProbeForm {m n : ℕ}
    (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (Q : GibbsOperator n) :
    LinearMap.BilinForm ℝ (FamilyCarrier m n) :=
  ∑ i, c i •
    (ceCurvatureBKMProbeForm D hpow (a i) Q).compl₁₂
      (LinearMap.proj i) (LinearMap.proj i)

@[simp] theorem finiteCEFamilyNOperatorCurvatureProbeForm_apply
    {m n : ℕ} (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (Q : GibbsOperator n)
    (x y : FamilyCarrier m n) :
    finiteCEFamilyNOperatorCurvatureProbeForm D hpow a c Q x y =
      ∑ i, c i • ceCurvatureBKMProbeForm D hpow (a i) Q (x i) (y i) := by
  simp only [finiteCEFamilyNOperatorCurvatureProbeForm,
    LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.compl₁₂_apply, LinearMap.proj_apply]

theorem finiteCEFamilyNOperatorDissipativeForm_symm
    {m n : ℕ} (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (x y : FamilyCarrier m n) :
    finiteCEFamilyNOperatorDissipativeForm D hpow a c x y =
      finiteCEFamilyNOperatorDissipativeForm D hpow a c y x := by
  rw [finiteCEFamilyNOperatorDissipativeForm_apply,
    finiteCEFamilyNOperatorDissipativeForm_apply]
  exact centeredBKMRealCovariance_symm D hpow _ _

theorem finiteCEFamilyNOperatorDissipativeForm_nonneg
    {m n : ℕ} (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (x : FamilyCarrier m n) :
    0 ≤ finiteCEFamilyNOperatorDissipativeForm D hpow a c x x := by
  rw [finiteCEFamilyNOperatorDissipativeForm_apply,
    centeredBKMRealCovariance_self]
  exact D.kuboMoriPairing_self_re_nonneg
    (centeredStatistic D (finiteGibbsCEFamilyNOperatorReadoutLinear a c x)) hpow

theorem finiteCEFamilyNOperatorCurvatureProbeForm_skew
    {m n : ℕ} (D : SouriauOnsagerBKM.FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (Q : GibbsOperator n)
    (x y : FamilyCarrier m n) :
    finiteCEFamilyNOperatorCurvatureProbeForm D hpow a c Q x y =
      -finiteCEFamilyNOperatorCurvatureProbeForm D hpow a c Q y x := by
  rw [finiteCEFamilyNOperatorCurvatureProbeForm_apply,
    finiteCEFamilyNOperatorCurvatureProbeForm_apply]
  calc
    (∑ i, c i • ceCurvatureBKMProbeForm D hpow (a i) Q (x i) (y i)) =
        ∑ i, c i • -ceCurvatureBKMProbeForm D hpow (a i) Q (y i) (x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ceCurvatureBKMProbeForm_skew]
    _ = -(∑ i, c i • ceCurvatureBKMProbeForm D hpow (a i) Q (y i) (x i)) := by
          simp_rw [smul_neg]
          rw [← Finset.sum_neg_distrib]

/-- The finite Gibbs CE Onsager system on independent component directions.
The reversible form is the weighted component-curvature sum, not a
curvature-of-a-weighted-sum surrogate. -/
def finiteGibbsCEFamilyNOperatorSystem {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (a : Fin m → GibbsOperator n) (c : Fin m → ℝ)
    (Q : GibbsOperator n) :
    OnsagerCasimirSystem (FamilyCarrier m n) where
  dissipative := finiteCEFamilyNOperatorDissipativeForm
    (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ) a c
  reversible := finiteCEFamilyNOperatorCurvatureProbeForm
    (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ) a c Q
  dissipative_symm := finiteCEFamilyNOperatorDissipativeForm_symm _ _ a c
  reversible_skew := finiteCEFamilyNOperatorCurvatureProbeForm_skew _ _ a c Q
  dissipative_nonneg := finiteCEFamilyNOperatorDissipativeForm_nonneg _ _ a c

theorem finiteGibbsCEFamilyNOperatorSystem_entropy
    {m n : ℕ} (H : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (Q : GibbsOperator n) (x : FamilyCarrier m n) :
    (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).totalGenerator x x =
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c x)
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c x) ∧
    0 ≤ (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).totalGenerator x x := by
  constructor
  · rw [(finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).entropy_production_eq]
    exact finiteCEFamilyNOperatorDissipativeForm_apply _ _ a c x x
  · exact
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).entropy_production_nonneg x

/-- The weighted pairwise response for independent Fréchet directions on
the components of an `NOperatorForm` family. -/
def finiteGibbsCEFamilyNOperatorPairwiseBKMResponse {m n : ℕ}
    (H : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ)
    (D E : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n)) : ℝ :=
  ∑ i, c i • ∑ j, c j •
    centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ)
      (finiteGibbsCEFamilyComponentForm a i
        (finiteCEFrechetDirection (D i)))
      (finiteGibbsCEFamilyComponentForm a j
        (finiteCEFrechetDirection (E j)))

theorem finiteGibbsCEFamilyNOperatorPairwiseBKMResponse_eq_aggregateBKM
    {m n : ℕ} (H : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ)
    (D E : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n)) :
    finiteGibbsCEFamilyNOperatorPairwiseBKMResponse H hH hZ a c D E =
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c
          (finiteCEFrechetFamilyDirection D))
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c
          (finiteCEFrechetFamilyDirection E)) := by
  let density := faithfulGibbsDensity H hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  let readoutD : Fin m → GibbsOperator n := fun i =>
    finiteGibbsCEFamilyComponentForm a i
      (finiteCEFrechetDirection (D i))
  let readoutE : Fin m → GibbsOperator n := fun i =>
    finiteGibbsCEFamilyComponentForm a i
      (finiteCEFrechetDirection (E i))
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
  unfold finiteGibbsCEFamilyNOperatorPairwiseBKMResponse
  rw [finiteGibbsCEFamilyNOperatorReadoutLinear_apply,
    finiteGibbsCEFamilyNOperatorReadoutLinear_apply]
  simpa [density, hpow, readoutD, readoutE,
    finiteCEFrechetFamilyDirection,
    finiteGibbsCEFamilyComponentForm_apply] using hcovarianceExpansion.symm

/-- The independent-direction pairwise CE-family response is both the
dissipation of the product-carrier Onsager system and the mixed Hessian of
the finite Gibbs log-partition. -/
theorem finiteGibbsCEFamilyNOperatorSystem_pairwise_eq_dissipation_hessian
    {m n : ℕ} (H : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (Q : GibbsOperator n)
    (D E : Fin m → FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD : IsSelfAdjoint
      (finiteGibbsCEFamilyNOperatorReadoutLinear a c
        (finiteCEFrechetFamilyDirection D))) :
    finiteGibbsCEFamilyNOperatorPairwiseBKMResponse H hH hZ a c D E =
      (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative
        (finiteCEFrechetFamilyDirection D)
        (finiteCEFrechetFamilyDirection E) ∧
    finiteGibbsCEFamilyNOperatorPairwiseBKMResponse H hH hZ a c D E =
      (secondFDerivLogPartitionReadout H
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c
          (finiteCEFrechetFamilyDirection D))
        (finiteGibbsCEFamilyNOperatorReadoutLinear a c
          (finiteCEFrechetFamilyDirection E))).re := by
  let x := finiteCEFrechetFamilyDirection D
  let y := finiteCEFrechetFamilyDirection E
  let aggregateD := finiteGibbsCEFamilyNOperatorReadoutLinear a c x
  let aggregateE := finiteGibbsCEFamilyNOperatorReadoutLinear a c y
  have hpair := finiteGibbsCEFamilyNOperatorPairwiseBKMResponse_eq_aggregateBKM
    H hH hZ a c D E
  have hdiss :
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
          (continuous_faithfulGibbsDensity_rpow H hH hZ)
          aggregateD aggregateE =
        (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative x y := by
    change centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        aggregateD aggregateE =
      finiteCEFamilyNOperatorDissipativeForm
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ) a c x y
    rw [finiteCEFamilyNOperatorDissipativeForm_apply]
  have hhess := secondFDeriv_logPartition_apply_eq_centeredBKM
    H hH hZ aggregateD aggregateE (by simpa [aggregateD, x] using hD)
  constructor
  · calc
      finiteGibbsCEFamilyNOperatorPairwiseBKMResponse H hH hZ a c D E =
          centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
            (continuous_faithfulGibbsDensity_rpow H hH hZ)
            aggregateD aggregateE := hpair
      _ = (finiteGibbsCEFamilyNOperatorSystem H hH hZ a c Q).dissipative x y :=
        hdiss
  · calc
      finiteGibbsCEFamilyNOperatorPairwiseBKMResponse H hH hZ a c D E =
          centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
            (continuous_faithfulGibbsDensity_rpow H hH hZ)
            aggregateD aggregateE := hpair
      _ = (secondFDerivLogPartitionReadout H aggregateD aggregateE).re :=
        hhess.symm

end InfoGeometry.Canonical.CEBKMOnsagerGibbsNOperatorFamily
