/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CEBKMOnsagerSystem
import InfoGeometry.Canonical.CEOneFormNOperatorBridge
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
import InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
import InfoGeometry.Optics.OperatorDerivationForms

/-!
# Gibbs specialization of the finite CE Onsager system

This module specializes the proved CE Onsager system to the same normalized
finite Gibbs density used by the log-partition Hessian owner. It identifies
the Hessian on two Fréchet-induced CE directions with the dissipative form;
on the diagonal, the actual total-generator entropy production equals that
Hessian and is nonnegative. The reversible curvature term remains part of the
system and is removed from diagonal production only by its proved skewness.
-/

noncomputable section

namespace InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration

open InfoGeometry.Canonical.CEBKMOnsagerSystem
open InfoGeometry.Canonical.CEOneFormNOperatorBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Thermo.OnsagerClosure

variable {n : ℕ}

/-- Every component of a finite Gibbs CE family, encoded in the existing
`NOperatorForm` carrier, evaluates on a Fréchet-induced derivation as the
first Fréchet jet of that component. -/
theorem finiteGibbsCEFamily_component_eq_firstFrechetJet
    {m n : ℕ} (a : Fin m → GibbsOperator n)
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (x : GibbsOperator n) (i : Fin m) :
    ofCEFamily (realDerivationsLane (GibbsOperator n)) m
        (fun j => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a j))
        i () (finiteCEFrechetDirection D) =
      operatorFrechetJet 1 (D : GibbsOperator n → GibbsOperator n) x
        (fun _ : Fin 1 => a i) := by
  change component (K := realDerivationsLane (GibbsOperator n)) m
      (fun j => exteriorDerivativeZero
        (realDerivationsLane (GibbsOperator n)) (a j)) i
      (finiteCEFrechetDirection D) = _
  rw [component_apply]
  symm
  exact operatorFrechetJet_one_apply_eq_exteriorDerivativeZero D x (a i)

/-- The mixed finite Gibbs Hessian for any two components of a finite CE
family is the centered BKM covariance of their genuine extracted
`Op1Form`s. The self-adjointness condition remains on the first component
only, as required by the Hessian owner. -/
theorem finiteGibbsCEFamily_pairwise_hessian_eq_centeredBKM
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (D E : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (i j : Fin m)
    (hD : IsSelfAdjoint
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection D))) :
    (secondFDerivLogPartitionReadout H
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection D))
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) j
        (finiteCEFrechetDirection E))).re =
    centeredBKMOperatorBilinForm
      (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ)
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i)
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) j)
      (finiteCEFrechetDirection D) (finiteCEFrechetDirection E) := by
  exact secondFDeriv_logPartition_pullback_eq_centeredBKMOperatorBilinForm
    H hH hZ
    (component (K := realDerivationsLane (GibbsOperator n)) m
      (fun k => exteriorDerivativeZero
        (realDerivationsLane (GibbsOperator n)) (a k)) i)
    (component (K := realDerivationsLane (GibbsOperator n)) m
      (fun k => exteriorDerivativeZero
        (realDerivationsLane (GibbsOperator n)) (a k)) j)
    (finiteCEFrechetDirection D) (finiteCEFrechetDirection E) hD

/-- The diagonal-index Gibbs Hessian of a finite CE family component is the
dissipative form of the concrete Gibbs CE Onsager system built from that
same component. -/
theorem finiteGibbsCEFamily_diagonal_eq_onsagerDissipation
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (Q : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (D E : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (i : Fin m)
    (hD : IsSelfAdjoint
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection D))) :
    (secondFDerivLogPartitionReadout H
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection D))
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection E))).re =
    (finiteCEOnsagerSystem (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ) (a i) Q).dissipative
      (finiteCEFrechetDirection D) (finiteCEFrechetDirection E) := by
  simpa [finiteCEOnsagerSystem, centeredCEBKMForm_apply,
    centeredBKMOperatorBilinForm, finiteCEOperatorForm, component_apply] using
    (finiteGibbsCEFamily_pairwise_hessian_eq_centeredBKM
      H a hH hZ D E i i hD)

/-- The diagonal Gibbs Hessian of a selected finite CE family component is
the total-generator entropy production of its concrete Onsager system. -/
theorem finiteGibbsCEFamily_diagonal_eq_totalGenerator
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (Q : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (i : Fin m)
    (hD : IsSelfAdjoint
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection D))) :
    (finiteCEOnsagerSystem (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ) (a i) Q).totalGenerator
        (finiteCEFrechetDirection D) (finiteCEFrechetDirection D) =
      (secondFDerivLogPartitionReadout H
        (component (K := realDerivationsLane (GibbsOperator n)) m
          (fun k => exteriorDerivativeZero
            (realDerivationsLane (GibbsOperator n)) (a k)) i
          (finiteCEFrechetDirection D))
        (component (K := realDerivationsLane (GibbsOperator n)) m
          (fun k => exteriorDerivativeZero
            (realDerivationsLane (GibbsOperator n)) (a k)) i
          (finiteCEFrechetDirection D))).re := by
  have hEntropy := finiteCEOnsagerSystem_entropy
    (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ) (a i) Q
    (finiteCEFrechetDirection D)
  calc
    (finiteCEOnsagerSystem (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ) (a i) Q).totalGenerator
        (finiteCEFrechetDirection D) (finiteCEFrechetDirection D) =
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D)) := hEntropy.1
    _ = (secondFDerivLogPartitionReadout H
        (component (K := realDerivationsLane (GibbsOperator n)) m
          (fun k => exteriorDerivativeZero
            (realDerivationsLane (GibbsOperator n)) (a k)) i
          (finiteCEFrechetDirection D))
        (component (K := realDerivationsLane (GibbsOperator n)) m
          (fun k => exteriorDerivativeZero
            (realDerivationsLane (GibbsOperator n)) (a k)) i
          (finiteCEFrechetDirection D))).re := by
      simpa [centeredBKMOperatorBilinForm, finiteCEOperatorForm,
        component_apply] using
        (finiteGibbsCEFamily_pairwise_hessian_eq_centeredBKM
          H a hH hZ D D i i hD).symm

/-- Each component's real diagonal Gibbs Hessian is nonnegative, by the
entropy-production theorem for its actual finite CE Onsager system. -/
theorem finiteGibbsCEFamily_diagonal_hessian_nonneg
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (Q : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (i : Fin m)
    (hD : IsSelfAdjoint
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection D))) :
    0 ≤ (secondFDerivLogPartitionReadout H
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection D))
      (component (K := realDerivationsLane (GibbsOperator n)) m
        (fun k => exteriorDerivativeZero
          (realDerivationsLane (GibbsOperator n)) (a k)) i
        (finiteCEFrechetDirection D))).re := by
  rw [← finiteGibbsCEFamily_diagonal_eq_totalGenerator
    H a Q hH hZ D i hD]
  exact (finiteCEOnsagerSystem (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ) (a i) Q).entropy_production_nonneg
      (finiteCEFrechetDirection D)

/-- The CE readout of a finite real linear combination of observables is the
same finite real linear combination of their CE readouts. -/
theorem finiteGibbsCEFamily_weightedReadout_eq
    {m n : ℕ} (a : Fin m → GibbsOperator n) (c : Fin m → ℝ)
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n)) :
    (∑ i, c i • finiteCEOperatorForm n (a i)
      (finiteCEFrechetDirection D)) =
      finiteCEOperatorForm n (∑ i, c i • a i)
        (finiteCEFrechetDirection D) := by
  change (∑ i, c i •
      exteriorDerivativeZero (realDerivationsLane (GibbsOperator n))
        (a i) (finiteCEFrechetDirection D)) =
    exteriorDerivativeZero (realDerivationsLane (GibbsOperator n))
      (∑ i, c i • a i) (finiteCEFrechetDirection D)
  simp only [map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, exteriorDerivativeZero_apply]

/-- A finite real linear combination of family CE readouts has nonnegative
centered BKM quadratic response. The sum is identified with the CE readout
of the summed observable, so positivity is applied to the actual finite
operator rather than supplied as a property field. -/
theorem finiteGibbsCEFamily_aggregateBKM_quadratic_nonneg
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (D : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H) :
    0 ≤ centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ)
      (∑ i, c i • finiteCEOperatorForm n (a i)
        (finiteCEFrechetDirection D))
      (∑ i, c i • finiteCEOperatorForm n (a i)
        (finiteCEFrechetDirection D)) := by
  let b : GibbsOperator n := ∑ i, c i • a i
  have hsum := finiteGibbsCEFamily_weightedReadout_eq a c D
  have hsum' :
      (∑ i, c i • finiteCEOperatorForm n (a i)
        (finiteCEFrechetDirection D)) =
      finiteCEOperatorForm n b (finiteCEFrechetDirection D) := by
    simpa [b] using hsum
  rw [hsum', ← centeredCEBKMForm_apply]
  exact centeredCEBKMForm_nonneg (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ) b
    (finiteCEFrechetDirection D)

/-- The coefficient-weighted quadratic response of a finite Gibbs CE family
is exactly the nested coefficient-weighted sum of its pairwise centered BKM
responses. Its nonnegativity is the previously proved aggregate BKM result. -/
theorem finiteGibbsCEFamily_pairwise_quadratic_eq_aggregateBKM
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (D : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H) :
    (∑ i, c i • ∑ j, c j •
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a j) (finiteCEFrechetDirection D))) =
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (∑ i, c i • finiteCEOperatorForm n (a i)
          (finiteCEFrechetDirection D))
        (∑ i, c i • finiteCEOperatorForm n (a i)
          (finiteCEFrechetDirection D)) ∧
    0 ≤ ∑ i, c i • ∑ j, c j •
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a j) (finiteCEFrechetDirection D)) := by
  let density := faithfulGibbsDensity H hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  let direction := finiteCEFrechetDirection D
  let readout : Fin m → GibbsOperator n :=
    fun i => finiteCEOperatorForm n (a i) direction
  let quotientReadout : Fin m →
      GibbsOperator n ⧸ BKMScalarGaugeQuotient.scalarGauge n :=
    fun i => Submodule.Quotient.mk (readout i)
  have hquotientSum :
      (∑ i, c i • quotientReadout i) =
        (BKMScalarGaugeQuotient.scalarGauge n).mkQ
          (∑ i, c i • readout i) := by
    change (∑ i, c i •
        (BKMScalarGaugeQuotient.scalarGauge n).mkQ (readout i)) = _
    rw [map_sum]
    simp only [map_smul]
  have hbilinearExpansion :
      BKMScalarGaugeQuotient.quotientBKMForm density hpow
          (∑ i, c i • quotientReadout i)
          (∑ j, c j • quotientReadout j) =
        ∑ i, c i • ∑ j, c j •
          BKMScalarGaugeQuotient.quotientBKMForm density hpow
            (quotientReadout i) (quotientReadout j) := by
    let B := BKMScalarGaugeQuotient.quotientBKMForm density hpow
    have houter :
        B (∑ i, c i • quotientReadout i) =
          ∑ i, c i • B (quotientReadout i) := by
      simp only [map_sum, map_smul]
    have hinner (i : Fin m) :
        B (quotientReadout i) (∑ j, c j • quotientReadout j) =
          ∑ j, c j • B (quotientReadout i) (quotientReadout j) := by
      simp only [map_sum, map_smul]
    calc
      B (∑ i, c i • quotientReadout i)
          (∑ j, c j • quotientReadout j) =
        ∑ i, c i • B (quotientReadout i)
          (∑ j, c j • quotientReadout j) := by
            have h := congrArg
              (fun f : (GibbsOperator n ⧸
                BKMScalarGaugeQuotient.scalarGauge n) →ₗ[ℝ] ℝ =>
                  f (∑ j, c j • quotientReadout j)) houter
            simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using h
      _ = ∑ i, c i • ∑ j, c j •
            B (quotientReadout i) (quotientReadout j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hinner i]
  have hcovarianceExpansion :
      centeredBKMRealCovariance density hpow
          (∑ i, c i • readout i) (∑ i, c i • readout i) =
        ∑ i, c i • ∑ j, c j •
          centeredBKMRealCovariance density hpow (readout i) (readout j) := by
    calc
      centeredBKMRealCovariance density hpow
          (∑ i, c i • readout i) (∑ i, c i • readout i) =
        BKMScalarGaugeQuotient.quotientBKMForm density hpow
          ((BKMScalarGaugeQuotient.scalarGauge n).mkQ
            (∑ i, c i • readout i))
          ((BKMScalarGaugeQuotient.scalarGauge n).mkQ
            (∑ i, c i • readout i)) := by
              change centeredBKMRealCovariance density hpow
                  (∑ i, c i • readout i) (∑ i, c i • readout i) =
                BKMScalarGaugeQuotient.quotientBKMForm density hpow
                  (Submodule.Quotient.mk (∑ i, c i • readout i))
                  (Submodule.Quotient.mk (∑ i, c i • readout i))
              rw [BKMScalarGaugeQuotient.quotientBKMForm_mk]
      _ = BKMScalarGaugeQuotient.quotientBKMForm density hpow
            (∑ i, c i • quotientReadout i)
            (∑ j, c j • quotientReadout j) := by
              rw [← hquotientSum]
      _ = ∑ i, c i • ∑ j, c j •
            BKMScalarGaugeQuotient.quotientBKMForm density hpow
              (quotientReadout i) (quotientReadout j) := hbilinearExpansion
      _ = ∑ i, c i • ∑ j, c j •
            centeredBKMRealCovariance density hpow (readout i) (readout j) := by
              simp [quotientReadout, BKMScalarGaugeQuotient.quotientBKMForm_mk]
  constructor
  · simpa [density, hpow, direction, readout] using hcovarianceExpansion.symm
  · rw [← hcovarianceExpansion]
    exact finiteGibbsCEFamily_aggregateBKM_quadratic_nonneg
      H a c D hH hZ

/-- The finite CE Onsager system at the faithful density generated by `H`. -/
def finiteGibbsCEOnsagerSystem
    (H : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H) (a Q : GibbsOperator n) :
    OnsagerCasimirSystem (Carrier n) :=
  finiteCEOnsagerSystem (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ) a Q

/-- The mixed Gibbs log-partition Hessian on two Fréchet-induced CE
directions is the dissipative part of the CE Onsager system at the same
faithful Gibbs density. The Hessian owner's one-sided self-adjointness
condition is retained exactly. -/
theorem finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (D E : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD : IsSelfAdjoint
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))) :
    (secondFDerivLogPartitionReadout H
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))
      (finiteCEOperatorForm n a (finiteCEFrechetDirection E))).re =
    (finiteGibbsCEOnsagerSystem H hH hZ a Q).dissipative
      (finiteCEFrechetDirection D) (finiteCEFrechetDirection E) := by
  rw [secondFDeriv_logPartition_apply_eq_centeredBKM
    H hH hZ _ _ hD]
  change centeredBKMRealCovariance
      (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ)
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))
      (finiteCEOperatorForm n a (finiteCEFrechetDirection E)) =
    centeredCEBKMForm (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ) a
      (finiteCEFrechetDirection D) (finiteCEFrechetDirection E)
  exact (centeredCEBKMForm_apply (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ) a
    (finiteCEFrechetDirection D) (finiteCEFrechetDirection E)).symm

/-- The diagonal total-generator production equals the real Gibbs Hessian
for a Fréchet-induced CE direction. -/
theorem finiteGibbsCEOnsagerSystem_diagonal_eq_logPartitionHessian
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD : IsSelfAdjoint
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))) :
    (finiteGibbsCEOnsagerSystem H hH hZ a Q).totalGenerator
        (finiteCEFrechetDirection D) (finiteCEFrechetDirection D) =
      (secondFDerivLogPartitionReadout H
        (finiteCEOperatorForm n a (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n a (finiteCEFrechetDirection D))).re := by
  rw [(finiteGibbsCEOnsagerSystem H hH hZ a Q).entropy_production_eq]
  exact (finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian
    H a Q hH hZ D D hD).symm

/-- The finite real Gibbs log-partition Hessian on a Fréchet-induced CE
direction is nonnegative. -/
theorem finiteGibbsCEOnsagerSystem_diagonal_logPartitionHessian_nonneg
    (H a Q : GibbsOperator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hD : IsSelfAdjoint
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))) :
    0 ≤ (secondFDerivLogPartitionReadout H
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))
      (finiteCEOperatorForm n a (finiteCEFrechetDirection D))).re := by
  rw [← finiteGibbsCEOnsagerSystem_diagonal_eq_logPartitionHessian
    H a Q hH hZ D hD]
  exact (finiteGibbsCEOnsagerSystem H hH hZ a Q).entropy_production_nonneg
    (finiteCEFrechetDirection D)

/-- The finite-family pairwise BKM quadratic is the dissipative response of
the Gibbs CE Onsager system at the weighted aggregate observable, and equals
its real log-partition Hessian under self-adjointness of the aggregate
readout. Nonnegativity is inherited from the proved finite BKM positivity. -/
theorem finiteGibbsCEFamily_pairwise_quadratic_eq_aggregateOnsagerDissipation_hessian
    {m n : ℕ} (H : GibbsOperator n) (a : Fin m → GibbsOperator n)
    (c : Fin m → ℝ) (Q : GibbsOperator n)
    (D : FrechetOperatorDerivation ℂ (GibbsOperator n))
    (hH : IsSelfAdjoint H) (hZ : 0 < gibbsPartitionReal H)
    (hD : IsSelfAdjoint
      (finiteCEOperatorForm n (∑ i, c i • a i)
        (finiteCEFrechetDirection D))) :
    (∑ i, c i • ∑ j, c j •
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a j) (finiteCEFrechetDirection D))) =
      (finiteGibbsCEOnsagerSystem H hH hZ (∑ i, c i • a i) Q).dissipative
        (finiteCEFrechetDirection D) (finiteCEFrechetDirection D) ∧
    (∑ i, c i • ∑ j, c j •
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a j) (finiteCEFrechetDirection D))) =
      (secondFDerivLogPartitionReadout H
        (finiteCEOperatorForm n (∑ i, c i • a i)
          (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (∑ i, c i • a i)
          (finiteCEFrechetDirection D))).re ∧
    0 ≤ ∑ i, c i • ∑ j, c j •
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n (a i) (finiteCEFrechetDirection D))
        (finiteCEOperatorForm n (a j) (finiteCEFrechetDirection D)) := by
  let b : GibbsOperator n := ∑ i, c i • a i
  let direction := finiteCEFrechetDirection D
  let pairwiseQuadratic := ∑ i, c i • ∑ j, c j •
    centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
      (continuous_faithfulGibbsDensity_rpow H hH hZ)
      (finiteCEOperatorForm n (a i) direction)
      (finiteCEOperatorForm n (a j) direction)
  have hpair := finiteGibbsCEFamily_pairwise_quadratic_eq_aggregateBKM
    H a c D hH hZ
  have hreadout := finiteGibbsCEFamily_weightedReadout_eq a c D
  have hdiss :
      centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        (finiteCEOperatorForm n b direction)
        (finiteCEOperatorForm n b direction) =
      (finiteGibbsCEOnsagerSystem H hH hZ b Q).dissipative direction direction := by
    rw [← centeredCEBKMForm_apply]
    rfl
  have hmain : pairwiseQuadratic =
      (finiteGibbsCEOnsagerSystem H hH hZ b Q).dissipative direction direction := by
    calc
      pairwiseQuadratic =
          centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
            (continuous_faithfulGibbsDensity_rpow H hH hZ)
            (∑ i, c i • finiteCEOperatorForm n (a i) direction)
            (∑ i, c i • finiteCEOperatorForm n (a i) direction) := by
              simpa [pairwiseQuadratic, direction] using hpair.1
      _ = centeredBKMRealCovariance (faithfulGibbsDensity H hH hZ)
            (continuous_faithfulGibbsDensity_rpow H hH hZ)
            (finiteCEOperatorForm n b direction)
            (finiteCEOperatorForm n b direction) := by
              rw [show (∑ i, c i • finiteCEOperatorForm n (a i) direction) =
                finiteCEOperatorForm n b direction by
                  simpa [b, direction] using hreadout]
      _ = (finiteGibbsCEOnsagerSystem H hH hZ b Q).dissipative
            direction direction := hdiss
  have hhess := finiteGibbsCEOnsagerSystem_dissipative_eq_logPartitionHessian
    H b Q hH hZ D D (by simpa [b] using hD)
  constructor
  · simpa [pairwiseQuadratic, b, direction] using hmain
  constructor
  · calc
      pairwiseQuadratic =
          (finiteGibbsCEOnsagerSystem H hH hZ b Q).dissipative direction direction := hmain
      _ = (secondFDerivLogPartitionReadout H
          (finiteCEOperatorForm n b direction)
          (finiteCEOperatorForm n b direction)).re := hhess.symm
  · simpa [pairwiseQuadratic, direction] using hpair.2

end InfoGeometry.Canonical.CEBKMOnsagerGibbsIntegration
