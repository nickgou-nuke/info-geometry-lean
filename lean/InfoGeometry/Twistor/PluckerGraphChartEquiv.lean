/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerInfinityChart

/-!
# Equivalence for the existing normalized Klein graph chart

This packages the existing forward construction and reconstruction theorem as
an actual equivalence. It is the single `p23 = 1` chart, not the entire affine
line space or a Schubert decomposition of the Grassmannian.
-/

namespace InfoGeometry.Twistor.PluckerGraphChartEquiv

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Twistor.PluckerInfinityChart

variable {R : Type*} [Field R]

/-- The existing graph coordinates give all and only normalized Klein vectors. -/
def normalizedGraphEquiv :
    Matrix (Fin 2) (Fin 2) R ≃ {P : Plucker6 R // kleinQ P = 0 ∧ P.p23 = 1} where
  toFun X := ⟨graphPlucker X, kleinQ_graphPlucker X, graphPlucker_p23 X⟩
  invFun P := chartMatrix P.1
  left_inv X := chartMatrix_graphPlucker X
  right_inv P := by
    apply Subtype.ext
    have h := reconstruct_of_klein P.1 P.2.1 (by rw [P.2.2]; exact one_ne_zero)
    rw [P.2.2] at h
    simpa only [scale, one_mul] using h.symm

end InfoGeometry.Twistor.PluckerGraphChartEquiv
