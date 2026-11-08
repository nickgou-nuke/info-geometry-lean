/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.Bridge
import InfoGeometry.Projective.Normalize
import InfoGeometry.Twistor.NullProjective

/-!
# Positive-measure null rays in twistor space

The source is restricted to projective positive-measure classes whose
normalized representative is null for the chosen quadratic form. This makes
the null condition explicit on the domain and allows nonzero quadratic forms.
-/

namespace InfoGeometry.Projective.TwistorBridge

open InfoGeometry.Krein
open InfoGeometry.Twistor

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Positive-measure projective classes represented by a null vector for `Q`.
The normalization is canonical for the projective class. -/
def PositiveMeasureNullProjectiveClass
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α)) :=
  {q : PositiveMeasure.Proj (α := α) //
    Q (InfoGeometry.Projective.positiveMeasureToEuclidean (α := α)
      (InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) q)) = 0}

/-- A positive-measure null ray defines its corresponding point in the
projectivized null cone of `Q`. -/
noncomputable def nullProjectiveClassToTwistor
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α)) :
    PositiveMeasureNullProjectiveClass (α := α) Q → TwistorSpace Q := by
  intro q
  let μ := InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) q.1
  let v := InfoGeometry.Projective.positiveMeasureToEuclidean (α := α) μ
  exact twistorMk Q v
    (InfoGeometry.Projective.positiveMeasureToEuclidean_ne_zero (α := α) μ)
    q.2

@[simp] theorem nullProjectiveClassToTwistor_val
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ α))
    (q : PositiveMeasureNullProjectiveClass (α := α) Q) :
    (nullProjectiveClassToTwistor (α := α) Q q).1 =
      Projectivization.mk ℝ
        (InfoGeometry.Projective.positiveMeasureToEuclidean (α := α)
          (InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) q.1))
        (InfoGeometry.Projective.positiveMeasureToEuclidean_ne_zero (α := α)
          (InfoGeometry.Projective.Normalize.normalizeOnProj (α := α) q.1)) := rfl

end InfoGeometry.Projective.TwistorBridge
