import Mathlib
import InfoGeometry.Canonical.CantorPlabicTwistorBridge
import InfoGeometry.Canonical.FiniteFisherRaoSquareRoot

/-!
# Fisher--Rao geometry of the positive Plücker channel law

The six positive Plücker minors determine a finite probability vector after
normalizing their squares.  This module packages that vector in the existing
finite Fisher--Rao owner and reads back its square-root isometry.  It makes no
claim that the resulting Fisher form is spacetime curvature or that the
amplituhedron canonical form is a probability measure.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PositivePluckerFisherBridge

open InfoGeometry.Canonical.CantorPlabicTwistorBridge
open InfoGeometry.Canonical.FiniteFisherRaoSquareRoot

abbrev PluckerMatrix := InfoGeometry.Projective.MatrixPluckerPositiveBridge.Matrix2x4

/-- The normalized squared Plücker channel law as a strictly positive
probability vector on the six active sectors. -/
def pluckerStrictProbability (M : PluckerMatrix)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) : StrictProbability (Fin 6) where
  probability := pluckerSectorProbability M
  probability_pos := pluckerSectorProbability_pos M hM
  sum_probability := by
    exact (pluckerSector_pou M hM).property.2

/-- The Fisher--Rao pairing on tangent directions to the six Plücker
probabilities. -/
def pluckerFisherPair (M : PluckerMatrix)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (u v : Fin 6 → ℝ) : ℝ :=
  (pluckerStrictProbability M hM).fisherPair u v

/-- The score associated to a tangent vector is its coordinatewise relative
variation with respect to the positive Plücker-channel probability. -/
def pluckerScore (M : PluckerMatrix)
    (_hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (u : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
  u i / pluckerSectorProbability M i

/-- The finite Fisher pairing is the expectation, under the Plücker-channel
law, of the product of the two score functions. -/
theorem pluckerFisherPair_eq_score_expectation (M : PluckerMatrix)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (u v : Fin 6 → ℝ) :
    pluckerFisherPair M hM u v =
      ∑ i : Fin 6, pluckerSectorProbability M i *
        pluckerScore M hM u i * pluckerScore M hM v i := by
  unfold pluckerFisherPair pluckerScore StrictProbability.fisherPair
  apply Finset.sum_congr rfl
  intro i hi
  have hp : pluckerSectorProbability M i ≠ 0 :=
    ne_of_gt (pluckerSectorProbability_pos M hM i)
  field_simp [hp, pluckerStrictProbability]
  rw [show (pluckerStrictProbability M hM).probability i =
    pluckerSectorProbability M i by rfl]

/-- The Fisher--Rao quadratic form of the normalized positive Plücker law is
nonnegative. -/
theorem pluckerFisherPair_nonneg (M : PluckerMatrix)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (v : Fin 6 → ℝ) :
    0 ≤ pluckerFisherPair M hM v v := by
  exact (pluckerStrictProbability M hM).fisherPair_self_nonnegative v

/-- Under the finite square-root amplitude coordinates, the Euclidean
pairing of differential vectors is exactly the Plücker Fisher--Rao pairing. -/
theorem pluckerFisherPair_eq_sqrt_amplitude_pair (M : PluckerMatrix)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (u v : Fin 6 → ℝ) :
    (pluckerStrictProbability M hM).euclideanPair
        ((pluckerStrictProbability M hM).twoSqrtDifferential u)
        ((pluckerStrictProbability M hM).twoSqrtDifferential v) =
      pluckerFisherPair M hM u v := by
  exact (pluckerStrictProbability M hM).euclideanPair_twoSqrtDifferential u v

/-- The square-root Plücker amplitude lies on the radius-two sphere, since
the six squared channel probabilities sum to one. -/
theorem plucker_sqrt_amplitude_sphere (M : PluckerMatrix)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∑ i : Fin 6,
      ((pluckerStrictProbability M hM).twoSqrtAmplitude i) ^ 2 = 4 := by
  exact (pluckerStrictProbability M hM).twoSqrtAmplitude_normSq

/-- Tangent directions to the normalized Plücker law have coordinate sum
zero and map to vectors orthogonal to the radius-two amplitude. -/
theorem plucker_sqrt_amplitude_tangent_orthogonal (M : PluckerMatrix)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) (v : Fin 6 → ℝ) (hv : ∑ i : Fin 6, v i = 0) :
    (pluckerStrictProbability M hM).euclideanPair
      (pluckerStrictProbability M hM).twoSqrtAmplitude
      ((pluckerStrictProbability M hM).twoSqrtDifferential v) = 0 := by
  exact (pluckerStrictProbability M hM).amplitude_orthogonal_differential ⟨v, hv⟩

end InfoGeometry.Canonical.PositivePluckerFisherBridge

end noncomputable section
