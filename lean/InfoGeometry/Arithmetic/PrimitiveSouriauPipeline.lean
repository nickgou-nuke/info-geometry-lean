/-
InfoGeometry/Arithmetic/PrimitiveSouriauPipeline.lean

Owner-target surface for the primitive/Souriau/projective arithmetic sidecar
stack.

This module bundles the already-installed witness-gated corridors:

* primitive finite Mellin/Gibbs readouts;
* Souriau zeta calibration;
* projective temperature inversion;
* prime/von-Mangoldt projective partition;
* projective relative-entropy readouts and Weyl-gauge decompositions;
* finite arithmetic KMS sockets.

It does not prove the Erdős primitive-set theorem, Bost-Connes theorem, KMS
existence/uniqueness, the prime number theorem, analytic continuation, or a
global KL/Jensen theorem.
-/

import InfoGeometry.Arithmetic.ArithmeticKMS
import InfoGeometry.Arithmetic.PrimitiveSouriauZeta
import InfoGeometry.Arithmetic.ProjectivePrimePartition
import InfoGeometry.Arithmetic.ProjectiveRelativeEntropy
import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Arithmetic.WeylArithmeticDivergence
import InfoGeometry.Thermodynamics.ProjectiveTemperature
import InfoGeometry.Thermodynamics.SouriauTemperatureProjective
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Arithmetic.PrimitiveSouriauPipeline

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.ArithmeticKMS
open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Arithmetic.PrimitiveSouriauZeta
open InfoGeometry.Arithmetic.ProjectivePrimePartition
open InfoGeometry.Arithmetic.ProjectiveRelativeEntropy
open InfoGeometry.Arithmetic.ProjectiveWeylGauge
open InfoGeometry.Arithmetic.WeylArithmeticDivergence
open InfoGeometry.Thermodynamics.ProjectiveTemperature

/-! ## 1. Bundled installed witness surface -/

/--
Bundled witness surface for the finite primitive/Souriau/projective arithmetic
pipeline.

All substantial mathematical claims remain in the supplied witnesses.  This
structure exists so graph/orchestration tooling can point at one owner surface
instead of many sidecars.
-/
structure PrimitiveSouriauPipelineWitness
    (State : Type*) where
  /-- Finite support under inspection. -/
  support : Finset ℕ

  /-- Two finite count profiles for Weyl/KL comparison. -/
  counts₁ : CountProfile
  counts₂ : CountProfile

  /-- Compact projective temperature. -/
  u : ℝ

  /-- The compact temperature lies in `(0, 1)`. -/
  u_mem : u ∈ Set.Ioo (0 : ℝ) 1

  /-- Souriau finite zeta calibration. -/
  souriau : PrimitiveSouriauZetaCalibration State

  /-- Projective prime/von-Mangoldt calibration. -/
  prime : ProjectivePrimeCalibration State

  /-- Projective Weyl-gauge calibration. -/
  weyl : ProjectiveWeylGaugeCalibration State

  /-- Projective arithmetic KMS witness. -/
  kms : ProjectiveArithmeticKMSWitness State

  /-- Compatibility between projective KMS flow and prime flow. -/
  kmsPrime : ProjectiveKMSPrimeCompatibility State

  /-- Arithmetic divergence readout induced by the Weyl calibration. -/
  divergenceReadout :
    ArithmeticDivergenceReadout :=
      readoutOfProjectiveWeylGaugeCalibration weyl

namespace PrimitiveSouriauPipelineWitness

variable {State : Type*}
variable (P : PrimitiveSouriauPipelineWitness State)

/-- In the compact projective sector, the inverse temperature lies in the cold finite regime. -/
theorem beta_cold :
    1 < betaInvert P.u :=
  one_lt_betaInvert_of_mem_Ioo_zero_one P.u_mem

/-- The finite Gibbs/KMS partition readout is nonnegative. -/
theorem projective_gibbs_nonneg :
    0 ≤ projectiveArithmeticGibbsPartition P.support P.u :=
  projectiveArithmeticGibbsPartition_nonneg P.support P.u

/-- The projective KMS readout is calibrated to the finite Gibbs partition. -/
theorem kms_flow_eq_gibbs :
    P.kms.projectiveModularFlowReadout (P.kms.stateOfFinset P.support) P.u =
      projectiveArithmeticGibbsPartition P.support P.u :=
  P.kms.projectiveModularFlowReadout_eq_gibbsPartition P.support P.u_mem

/-- The compatible prime flow is nonnegative. -/
theorem prime_flow_nonneg :
    0 ≤ P.kmsPrime.prime.modularFlowReadout
      (P.kmsPrime.prime.stateOfFinset P.support) P.u :=
  P.kmsPrime.primeFlow_nonneg P.support P.u_mem

/-- The calibrated projective prime flow is the finite projective prime partition. -/
theorem prime_flow_eq_projectivePrimePartition :
    P.prime.modularFlowReadout (P.prime.stateOfFinset P.support) P.u =
      projectivePrimePartition P.support P.u :=
  P.prime.flow_eq_projectivePrimePartition P.support P.u P.u_mem

/-- The calibrated Weyl readout factors into thermal scale and shape core. -/
theorem weyl_total_eq_scale_mul_shape :
    P.weyl.totalReadout
        (P.weyl.stateOfProfiles P.counts₁ P.counts₂ P.support) P.u =
      P.weyl.weylScaleReadout
          (P.weyl.stateOfProfiles P.counts₁ P.counts₂ P.support) P.u *
        P.weyl.shapeCoreReadout
          (P.weyl.stateOfProfiles P.counts₁ P.counts₂ P.support) P.u :=
  P.weyl.total_eq_scale_mul_shape P.counts₁ P.counts₂ P.support P.u

/-- The concrete Itakura-Saito shape readout is invariant under left Weyl scaling. -/
theorem itakura_shape_scale_left
    (c : ℝ) (hc : c ≠ 0) :
    projectiveItakuraSaitoDistance
        (fun n => c * P.counts₁ n) P.counts₂ P.support P.u =
      projectiveItakuraSaitoDistance P.counts₁ P.counts₂ P.support P.u :=
  projectiveItakuraSaitoDistance_scale_left P.counts₁ P.counts₂ P.support P.u c hc

/-- The concrete Itakura-Saito shape readout is invariant under right Weyl scaling. -/
theorem itakura_shape_scale_right
    (c : ℝ) (hc : c ≠ 0) :
    projectiveItakuraSaitoDistance
        P.counts₁ (fun n => c * P.counts₂ n) P.support P.u =
      projectiveItakuraSaitoDistance P.counts₁ P.counts₂ P.support P.u :=
  projectiveItakuraSaitoDistance_scale_right P.counts₁ P.counts₂ P.support P.u c hc

/-! ## 2. Owner target -/

/-- The owner target follows directly from the supplied witness bundle. -/
theorem primitiveSouriauPipelineOwnerTarget :
    ∀ (State : Type*) (P : PrimitiveSouriauPipelineWitness State),
      1 < betaInvert P.u ∧
      0 ≤ projectiveArithmeticGibbsPartition P.support P.u ∧
      P.kms.projectiveModularFlowReadout (P.kms.stateOfFinset P.support) P.u =
        projectiveArithmeticGibbsPartition P.support P.u ∧
      0 ≤ P.kmsPrime.prime.modularFlowReadout
        (P.kmsPrime.prime.stateOfFinset P.support) P.u ∧
      P.prime.modularFlowReadout (P.prime.stateOfFinset P.support) P.u =
        projectivePrimePartition P.support P.u ∧
      P.weyl.totalReadout
          (P.weyl.stateOfProfiles P.counts₁ P.counts₂ P.support) P.u =
        P.weyl.weylScaleReadout
            (P.weyl.stateOfProfiles P.counts₁ P.counts₂ P.support) P.u *
          P.weyl.shapeCoreReadout
            (P.weyl.stateOfProfiles P.counts₁ P.counts₂ P.support) P.u := by
  intro State P
  exact ⟨
    P.beta_cold,
    P.projective_gibbs_nonneg,
    P.kms_flow_eq_gibbs,
    P.prime_flow_nonneg,
    P.prime_flow_eq_projectivePrimePartition,
    P.weyl_total_eq_scale_mul_shape
  ⟩

end PrimitiveSouriauPipelineWitness

end InfoGeometry.Arithmetic.PrimitiveSouriauPipeline
