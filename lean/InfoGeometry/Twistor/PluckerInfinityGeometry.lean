/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.InfinityTwistor
import InfoGeometry.Twistor.PluckerPenroseIncidence
import InfoGeometry.Twistor.PluckerLorentzRealForm
import InfoGeometry.Twistor.PluckerBlockInversion

/-!
# Infinity-normalized intervals of actual twistor frames

The spinor frame may be arbitrary with nonzero infinity contraction.
Its determinant scales the entire decomposable bivector, and the two
infinity contractions cancel exactly in the normalized interval. The final
theorem identifies the real Minkowski null equation with nontrivial
intersection of the existing Penrose incidence submodules.
-/

namespace InfoGeometry.Twistor.PluckerInfinityGeometry

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorPlucker
open InfoGeometry.Twistor.InfinityTwistor
open InfoGeometry.Twistor.PluckerInfinityChart
open InfoGeometry.Twistor.PluckerPenroseIncidence
open InfoGeometry.Twistor.PluckerLorentzRealForm
open InfoGeometry.Twistor.PluckerBlockInversion
open InfoGeometry.Canonical.PauliHestenesSpinMomentum

/-- The covariant infinity form is the Klein-polar dual of the actual infinity
point. Its zero hyperplane cuts out the null boundary on the Klein quadric. -/
theorem infinityTwistor_eq_kleinPolar_infinity (Z W : Twistor4) :
    infinityTwistor Z W = kleinPolar (twistorPairPlucker Z W) infinityPlucker := by
  rw [kleinPolar_infinityPlucker]
  exact infinityTwistor_eq_plucker_p23 Z W

/-- The infinity form depends on the lower spinors and is unchanged by the
explicit incidence-convention adapter. -/
@[simp] theorem infinityTwistor_graphIncidence
    (X Y : ComplexSpacetime) (π ρ : Spinor2) :
    infinityTwistor (graphIncidence X π) (graphIncidence Y ρ) =
      infinityTwistor (0, π) (0, ρ) := by
  simp [infinityTwistor]

/-- An arbitrary spinor frame scales the graph bivector by its infinity pairing. -/
theorem twistorPairPlucker_graph_frame
    (X : ComplexSpacetime) (π ρ : Spinor2) :
    twistorPairPlucker (graphIncidence X π) (graphIncidence X ρ) =
      Plucker6.scale (infinityTwistor (0, π) (0, ρ)) (graphPlucker X) := by
  apply Plucker6.ext <;>
    simp [twistorPairPlucker, twistorProjectiveVector, pluckerLine, graphIncidence_apply,
      Plucker6.scale, graphPlucker_coordinates, infinityTwistor,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

/-- The infinity-normalized interval is independent of the two nondegenerate
spinor frames, including their independent homogeneous scales. -/
theorem normalizedInterval_twistor_frames (X Y : ComplexSpacetime)
    (π ρ η θ : Spinor2)
    (hπρ : infinityTwistor (0, π) (0, ρ) ≠ 0)
    (hηθ : infinityTwistor (0, η) (0, θ) ≠ 0) :
    normalizedInterval
        (twistorPairPlucker (graphIncidence X π) (graphIncidence X ρ))
        (twistorPairPlucker (graphIncidence Y η) (graphIncidence Y θ)) =
      (X - Y).det := by
  rw [twistorPairPlucker_graph_frame, twistorPairPlucker_graph_frame,
    normalizedInterval_scale _ _ hπρ hηθ _ _ (by simp) (by simp),
    normalizedInterval_graphPlucker]

/-- The real `(1,3)` interval vanishes exactly when the actual native Penrose
planes have a nonzero common vector. Coincident planes are included. -/
theorem minkowski_null_iff_incidence_planes_intersect (P Q : PauliParavector) :
    (P.energy - Q.energy) ^ 2 - (P.px - Q.px) ^ 2 -
        (P.py - Q.py) ^ 2 - (P.pz - Q.pz) ^ 2 = 0 ↔
      incidencePlane P.pauliMatrix ⊓ incidencePlane Q.pauliMatrix ≠ ⊥ := by
  have h := det_sub_eq_zero_iff_incidencePlane_inf_ne_bot P.pauliMatrix Q.pauliMatrix
  rw [← normalizedInterval_graphPlucker, normalizedInterval_pauli,
    Complex.ofReal_eq_zero] at h
  exact h

end InfoGeometry.Twistor.PluckerInfinityGeometry
