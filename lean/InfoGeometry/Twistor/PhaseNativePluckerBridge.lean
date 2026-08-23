import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
import InfoGeometry.Projective.KleinQuadricPlucker

/-!
# Native phase-to-Plücker bridge

The six coordinates of the native chiral phase carrier are read directly as
the native `Plucker6` coordinates.  The sign on `p13` is forced by the
ordering `01,02,03,12,13,23`; it makes the Klein quadratic equal to the
chiral mixed pairing.

This owner only connects existing carriers.  It does not assert a global
projective quotient or a decomposability converse without a chart hypothesis.
-/

namespace InfoGeometry.Twistor.PhaseNativePluckerBridge

open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

abbrev Phase :=
  InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace.Phase

abbrev Plucker6 :=
  InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ

noncomputable def phaseToPlucker6 (X : Phase) : Plucker6 where
  p01 := X.1 0
  p02 := X.1 1
  p03 := X.1 2
  p12 := X.2 2
  p13 := -X.2 1
  p23 := X.2 0

@[simp] theorem phaseToPlucker6_p01 (X : Phase) :
    (phaseToPlucker6 X).p01 = X.1 0 := rfl

@[simp] theorem phaseToPlucker6_p13 (X : Phase) :
    (phaseToPlucker6 X).p13 = -X.2 1 := rfl

theorem kleinQ_phaseToPlucker6 (X : Phase) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 X) =
      chiralPairing X.1 X.2 := by
  simp [phaseToPlucker6, chiralPairing, InfoGeometry.Algebra.Vec3.dot]
  ring

theorem phaseNull_iff_kleinNull (X : Phase) :
    chiralPairing X.1 X.2 = 0 ↔
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (phaseToPlucker6 X) = 0 := by
  rw [kleinQ_phaseToPlucker6]

theorem phaseNull_has_pluckerLine_of_q0_ne_zero
    (X : Phase)
    (hnull : chiralPairing X.1 X.2 = 0)
    (hq0 : X.1 0 ≠ 0) :
    ∃ U V : InfoGeometry.Projective.KleinQuadricPlucker.Vec4 ℝ,
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine U V =
        phaseToPlucker6 X := by
  apply InfoGeometry.Projective.KleinQuadricPlucker
    .kleinRel_exists_pluckerLine_of_p01_ne_zero
  · rw [kleinQ_phaseToPlucker6, hnull]
  · exact hq0

end InfoGeometry.Twistor.PhaseNativePluckerBridge
