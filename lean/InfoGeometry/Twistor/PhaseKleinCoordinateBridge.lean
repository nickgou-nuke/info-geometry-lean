import Mathlib
import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

/-!
# Six-coordinate Klein readout of the polarized phase carrier

This owner proves only the coordinate quadratic identity.  It does not assert
decomposability, projectivization, or a Grassmannian embedding.
-/

namespace InfoGeometry.Twistor.PhaseKleinCoordinateBridge

open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

noncomputable section

abbrev Vec := Fin 3 → ℝ
abbrev Phase := Vec × Vec

structure KleinCoordinates where
  p01 : ℝ
  p02 : ℝ
  p03 : ℝ
  p23 : ℝ
  p31 : ℝ
  p12 : ℝ

def kleinForm (p : KleinCoordinates) : ℝ :=
  p.p01 * p.p23 + p.p02 * p.p31 + p.p03 * p.p12

def phaseKleinCoordinates (x : Phase) : KleinCoordinates where
  p01 := x.1 0
  p02 := x.1 1
  p03 := x.1 2
  p23 := x.2 0
  p31 := x.2 1
  p12 := x.2 2

theorem kleinForm_phaseKleinCoordinates (x : Phase) :
    kleinForm (phaseKleinCoordinates x) =
      chiralPairing x.1 x.2 := by
  simp [kleinForm, phaseKleinCoordinates, chiralPairing, Vec3.dot]
  ring

theorem phase_null_implies_klein_null
    (x : Phase)
    (hx : chiralPairing x.1 x.2 = 0) :
    kleinForm (phaseKleinCoordinates x) = 0 := by
  rw [kleinForm_phaseKleinCoordinates, hx]

theorem klein_null_iff_phase_pairing_zero (x : Phase) :
    kleinForm (phaseKleinCoordinates x) = 0 ↔
      chiralPairing x.1 x.2 = 0 := by
  rw [kleinForm_phaseKleinCoordinates]

end
end InfoGeometry.Twistor.PhaseKleinCoordinateBridge
