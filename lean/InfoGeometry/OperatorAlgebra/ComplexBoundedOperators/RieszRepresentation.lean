import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ComplexDecomposition

/-!
# AFP Riesz representation adapter

This module records the Lean-native root used for the AFP
`Riesz_Representation` corridor.

The theorem authority here is mathlib's real positive
Riesz-Markov-Kakutani theorem on compactly supported continuous functions:

* `RealRMK.rieszMeasure`
* `RealRMK.integral_rieszMeasure`
* `RealRMK.rieszMeasure_integralPositiveLinearMap`
* `RealRMK.integralPositiveLinearMap_rieszMeasure`

This file intentionally does not claim the arbitrary complex dual theorem on
`C₀(X, ℂ)`.  AFP's complex-positive section can be reconstructed from this
real-positive root plus explicit real/imaginary decomposition, but that is a
separate proof obligation.
-/

open scoped CompactlySupported ENNReal NNReal Topology
open MeasureTheory

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace RieszRepresentation

open ComplexDecomposition

variable {X : Type*}
variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]

/--
Repository-facing name for mathlib's representing measure attached to a
positive real linear functional on `C_c(X, ℝ)`.
-/
noncomputable def realRieszMeasure
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) : Measure X :=
  RealRMK.rieszMeasure Λ

/--
AFP/RMK root theorem in Lean-native form: integrating against the representing
measure recovers the positive real linear functional.
-/
@[simp]
theorem integral_realRieszMeasure
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) (f : C_c(X, ℝ)) :
    ∫ x, f x ∂realRieszMeasure Λ = Λ f := by
  simp [realRieszMeasure]

/-- The representing measure produced by real RMK is regular. -/
instance regular_realRieszMeasure
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) :
    (realRieszMeasure Λ).Regular := by
  dsimp [realRieszMeasure]
  infer_instance

/--
The positive linear functional induced by a regular measure is represented by
that same measure.  This is the surjectivity direction of mathlib's real RMK
equivalence.
-/
@[simp]
theorem realRieszMeasure_integralPositiveLinearMap
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.Regular] :
    realRieszMeasure
        (CompactlySupportedContinuousMap.integralPositiveLinearMap μ) = μ := by
  simp [realRieszMeasure]

/--
The measure attached to a positive functional induces back the original
functional.  This is the injective/retraction direction of mathlib's real RMK
equivalence.
-/
@[simp]
theorem integralPositiveLinearMap_realRieszMeasure
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) :
    CompactlySupportedContinuousMap.integralPositiveLinearMap
        (realRieszMeasure Λ) = Λ := by
  simp [realRieszMeasure]

/--
Two regular measures are equal if they integrate every compactly supported
continuous real function in the same way.
-/
theorem measure_ext_of_integral_eq_on_compactlySupported
    {μ ν : Measure X} [μ.Regular] [ν.Regular]
    (hμν : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν :=
  Measure.ext_of_integral_eq_on_compactlySupported hμν

/--
The positive functional induced by regular measures is injective.
-/
theorem integralPositiveLinearMap_injective_on_regular
    {μ ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    [μ.Regular] [ν.Regular]
    (h :
      CompactlySupportedContinuousMap.integralPositiveLinearMap μ =
        CompactlySupportedContinuousMap.integralPositiveLinearMap ν) :
    μ = ν := by
  exact (RealRMK.integralPositiveLinearMap_inj (μ := μ) (ν := ν)).mp h

noncomputable def complexIntegralLinearMap
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    C_c(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := by
    exact integral_add' f.integrable g.integrable
  map_smul' c f := by
    simpa using (integral_smul (μ := μ) c (fun x => f x))

omit [T2Space X] [LocallyCompactSpace X] in
@[simp]
theorem complexIntegralLinearMap_apply
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(X, ℂ)) :
    complexIntegralLinearMap μ f = ∫ x, f x ∂μ := rfl

omit [T2Space X] [LocallyCompactSpace X] in
@[simp]
theorem complexIntegralLinearMap_ccOfReal
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(X, ℝ)) :
    complexIntegralLinearMap μ (ccOfReal f) = (∫ x, f x ∂μ : ℂ) := by
  rw [complexIntegralLinearMap_apply]
  simp

omit [T2Space X] [LocallyCompactSpace X] in
theorem complexIntegralLinearMap_eq_re_add_im
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(X, ℂ)) :
    complexIntegralLinearMap μ f =
      ((∫ x, (ccRe f) x ∂μ : ℝ) : ℂ) +
        ((∫ x, (ccIm f) x ∂μ : ℝ) : ℂ) * Complex.I := by
  rw [complexIntegralLinearMap_apply]
  simpa using (integral_re_add_im (𝕜 := ℂ) (μ := μ) f.integrable).symm

end RieszRepresentation
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
