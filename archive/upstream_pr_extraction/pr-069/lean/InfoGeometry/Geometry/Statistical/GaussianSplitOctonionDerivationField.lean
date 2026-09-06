import Mathlib
import InfoGeometry.Lie.SplitOctonionStandardDerivation

/-!
# Supplied Gaussian fields on split-octonion derivation coordinates

This owner does not choose a canonical Gaussian measure.  It packages a
supplied Gaussian measure on the existing fourteen-coordinate parameter
space and transports that measure through the native derivation equivalence.
-/

namespace InfoGeometry.Geometry.Statistical.GaussianSplitOctonionDerivationField

noncomputable section

open MeasureTheory
open ProbabilityTheory
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension

def derivationOfCoordinates : (Fin 14 → ℝ) →
    InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv

def derivationMeasure
    [MeasurableSpace InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations]
    (μ : Measure (Fin 14 → ℝ)) :
    Measure InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  Measure.map derivationOfCoordinates μ

structure GaussianDerivationEnsemble where
  measure : Measure (Fin 14 → ℝ)
  isGaussian : IsGaussian measure

def coordinateObservable (i : Fin 14) : (Fin 14 → ℝ) → ℝ :=
  fun p => p i

def coordinateCovariance (E : GaussianDerivationEnsemble)
    (i j : Fin 14) : ℝ :=
  covariance (coordinateObservable i) (coordinateObservable j) E.measure

theorem coordinateCovariance_symm (E : GaussianDerivationEnsemble)
    (i j : Fin 14) :
    coordinateCovariance E i j = coordinateCovariance E j i := by
  unfold coordinateCovariance coordinateObservable
  simpa only using
    (covariance_comm
      (X := fun p : Fin 14 → ℝ => p i)
      (Y := fun p : Fin 14 → ℝ => p j)
      (μ := E.measure))

theorem coordinateCovariance_diag_eq_variance
    (E : GaussianDerivationEnsemble) (i : Fin 14) :
    coordinateCovariance E i i =
      variance (coordinateObservable i) E.measure := by
  unfold coordinateCovariance
  exact covariance_self (measurable_pi_apply i).aemeasurable

theorem coordinateCovariance_diag_nonneg
    (E : GaussianDerivationEnsemble) (i : Fin 14) :
    0 ≤ coordinateCovariance E i i := by
  rw [coordinateCovariance_diag_eq_variance]
  exact variance_nonneg _ _

theorem derivationOfCoordinates_add (p q : Fin 14 → ℝ) :
    derivationOfCoordinates (p + q) =
      derivationOfCoordinates p + derivationOfCoordinates q := by
  exact (canonicalParameterLinearEquiv :
    (Fin 14 → ℝ) ≃ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations).map_add p q

set_option synthInstance.maxHeartbeats 100000 in
theorem derivationOfCoordinates_smul (r : ℝ) (p : Fin 14 → ℝ) :
    derivationOfCoordinates (r • p) = r • derivationOfCoordinates p := by
  change canonicalParameterLinearEquiv (r • p) = r • canonicalParameterLinearEquiv p
  exact canonicalParameterLinearEquiv.map_smul r p

theorem derivationOfCoordinates_injective :
    Function.Injective derivationOfCoordinates := by
  exact canonicalParameterLinearEquiv.injective

theorem derivationOfCoordinates_surjective :
    Function.Surjective derivationOfCoordinates := by
  exact canonicalParameterLinearEquiv.surjective

theorem derivationOfCoordinates_eq_zero_iff (p : Fin 14 → ℝ) :
    derivationOfCoordinates p = 0 ↔ p = 0 := by
  exact canonicalParameterLinearEquiv.map_eq_zero_iff

end
end InfoGeometry.Geometry.Statistical.GaussianSplitOctonionDerivationField
