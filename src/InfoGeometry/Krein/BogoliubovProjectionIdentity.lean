import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Bogoliubov identity from orthogonal projections

This file isolates the algebraic content of the positive-sector
Bogoliubov identity.  It does not identify this identity with a physical
four-wave-mixing or information-recovery statement.
-/

open ContinuousLinearMap

namespace InfoGeometry.Krein.BogoliubovProjectionIdentity

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Complementary orthogonal projections defining a fundamental symmetry. -/
structure ProjectionSplit (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] where
  positive : E →L[𝕜] E
  negative : E →L[𝕜] E
  resolution : positive + negative = 1
  positive_idempotent : positive.comp positive = positive
  negative_idempotent : negative.comp negative = negative
  negative_positive : negative.comp positive = 0
  positive_selfadjoint : adjoint positive = positive
  negative_selfadjoint : adjoint negative = negative

namespace ProjectionSplit

variable (p : ProjectionSplit (𝕜 := 𝕜) E)

/-- The other orthogonality equation follows from self-adjointness. -/
theorem positive_negative : p.positive.comp p.negative = 0 := by
  have h := congrArg adjoint p.negative_positive
  rw [ContinuousLinearMap.adjoint_comp, p.positive_selfadjoint,
    p.negative_selfadjoint] at h
  simpa using h

/-- The fundamental symmetry associated with the projection split. -/
def symmetry : E →L[𝕜] E := p.positive - p.negative

theorem positive_symmetry : p.positive.comp p.symmetry = p.positive := by
  dsimp [symmetry]
  rw [comp_sub, p.positive_idempotent, p.positive_negative, sub_zero]

/-- Positive and negative parts of an operator applied to the positive sector. -/
def transmission (T : E →L[𝕜] E) : E →L[𝕜] E :=
  p.positive.comp (T.comp p.positive)

def reflection (T : E →L[𝕜] E) : E →L[𝕜] E :=
  p.negative.comp (T.comp p.positive)

theorem image_decomposition (T : E →L[𝕜] E) :
    T.comp p.positive = p.transmission T + p.reflection T := by
  rw [transmission, reflection, ← add_comp, p.resolution]
  ext x
  simp

theorem symmetry_image_decomposition (T : E →L[𝕜] E) :
    p.symmetry.comp (T.comp p.positive) =
      p.transmission T - p.reflection T := by
  rw [symmetry, sub_comp, transmission, reflection]

theorem adjoint_transmission (T : E →L[𝕜] E) :
    adjoint (p.transmission T) =
      p.positive.comp ((adjoint T).comp p.positive) := by
  simp [transmission, ContinuousLinearMap.adjoint_comp, p.positive_selfadjoint,
    comp_assoc]

theorem adjoint_reflection (T : E →L[𝕜] E) :
    adjoint (p.reflection T) =
      p.positive.comp ((adjoint T).comp p.negative) := by
  simp [reflection, ContinuousLinearMap.adjoint_comp, p.positive_selfadjoint,
    p.negative_selfadjoint, comp_assoc]

theorem transmission_reflection_orthogonal (T : E →L[𝕜] E) :
    (adjoint (p.transmission T)).comp (p.reflection T) = 0 := by
  rw [adjoint_transmission, reflection]
  calc
    (p.positive.comp ((adjoint T).comp p.positive)).comp
        (p.negative.comp (T.comp p.positive))
      = (p.positive.comp (adjoint T)).comp
          ((p.positive.comp p.negative).comp (T.comp p.positive)) := by
            simp only [comp_assoc]
    _ = 0 := by rw [p.positive_negative]; simp

theorem reflection_transmission_orthogonal (T : E →L[𝕜] E) :
    (adjoint (p.reflection T)).comp (p.transmission T) = 0 := by
  rw [adjoint_reflection, transmission]
  calc
    (p.positive.comp ((adjoint T).comp p.negative)).comp
        (p.positive.comp (T.comp p.positive))
      = (p.positive.comp (adjoint T)).comp
          ((p.negative.comp p.positive).comp (T.comp p.positive)) := by
            simp only [comp_assoc]
    _ = 0 := by rw [p.negative_positive]; simp

/--
If `T` preserves the indefinite form induced by `positive - negative` on
vectors in the positive sector, then its transmission and reflection blocks
satisfy the Bogoliubov difference identity.

The hypothesis is stated as the compressed operator equation on the image of
`positive`; this is the precise algebraic premise used by the proof.
-/
theorem bogoliubov_difference (T : E →L[𝕜] E)
    (hMetric : (adjoint (T.comp p.positive)).comp
      (p.symmetry.comp (T.comp p.positive)) = p.positive) :
    (adjoint (p.transmission T)).comp (p.transmission T) -
      (adjoint (p.reflection T)).comp (p.reflection T) = p.positive := by
  have hAdjoint : adjoint (T.comp p.positive) =
      adjoint (p.transmission T) + adjoint (p.reflection T) := by
    rw [p.image_decomposition]
    rw [show adjoint (p.transmission T + p.reflection T) =
      star (p.transmission T + p.reflection T) by
        exact (star_eq_adjoint _).symm]
    rw [star_add, star_eq_adjoint, star_eq_adjoint]
  rw [hAdjoint, p.symmetry_image_decomposition] at hMetric
  have hExpand :
      (adjoint (p.transmission T) + adjoint (p.reflection T)).comp
        (p.transmission T - p.reflection T) =
      (adjoint (p.transmission T)).comp (p.transmission T) -
        (adjoint (p.reflection T)).comp (p.reflection T) := by
    calc
      _ = (adjoint (p.transmission T)).comp (p.transmission T) -
            (adjoint (p.transmission T)).comp (p.reflection T) +
            (adjoint (p.reflection T)).comp (p.transmission T) -
            (adjoint (p.reflection T)).comp (p.reflection T) := by
          simp only [add_comp, comp_sub]
          abel
      _ = (adjoint (p.transmission T)).comp (p.transmission T) -
            (adjoint (p.reflection T)).comp (p.reflection T) := by
          rw [p.transmission_reflection_orthogonal,
            p.reflection_transmission_orthogonal]
          abel
  rw [hExpand] at hMetric
  exact hMetric

end ProjectionSplit
end InfoGeometry.Krein.BogoliubovProjectionIdentity
