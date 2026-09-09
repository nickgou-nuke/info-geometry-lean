import Mathlib
import InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge
import InfoGeometry.Canonical.TwoSheetComplexPolarization

/-!
# Hestenes--Krein phase on the real Cl(5,5) Fock envelope

The repository already owns a five-mode real matrix/Fock envelope and a native
Hestenes phase on it.  This file only exposes that theorem-owned operator as the
Fock-side internal complex structure for the QCD/Hestenes parallel lane.

No complexification of `Cl(5,5)` is introduced.  No `SU(3)` action on the
32-dimensional master carrier is postulated here.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDHestenesKreinFockPhaseBridge

open InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.TwoSheetComplexPolarization
open InfoGeometry.Clifford.Cl11TensorTower

abbrev FockMat := MasterMat32

/-- Fock-side internal Hestenes complex axis. -/
def fockJ : FockMat := masterHestenesPhase

/-- The Fock-side Hestenes axis squares to minus the identity. -/
@[simp] theorem fockJ_sq : fockJ * fockJ = -(1 : FockMat) := by
  exact masterHestenesPhase_sq

/-- The Fock Hestenes axis anticommutes with the master chirality grading. -/
theorem fockJ_anticomm_chirality :
    fockJ * globalChirality 5 + globalChirality 5 * fockJ = 0 := by
  exact masterHestenesPhase_anticomm_chirality

/-- The internal complex axis swaps the two chiral projectors by left action. -/
theorem fockJ_mul_chiralProjPlus :
    fockJ * chiralProjPlus 5 = chiralProjMinus 5 * fockJ := by
  exact masterHestenesPhase_mul_chiralProjPlus

theorem fockJ_mul_chiralProjMinus :
    fockJ * chiralProjMinus 5 = chiralProjPlus 5 * fockJ := by
  exact masterHestenesPhase_mul_chiralProjMinus

/-- Conjugation by the Hestenes phase exchanges the chiral projectors up to the
expected minus sign coming from `J^2=-1`. -/
theorem fockJ_conj_chiralProjPlus :
    fockJ * chiralProjPlus 5 * fockJ = -(chiralProjMinus 5) := by
  exact masterHestenesPhase_mul_chiralProjPlus_mul_phase

theorem fockJ_conj_chiralProjMinus :
    fockJ * chiralProjMinus 5 * fockJ = -(chiralProjPlus 5) := by
  exact masterHestenesPhase_mul_chiralProjMinus_mul_phase

/-- The master Hestenes phase commutes with the square of the embedded three-mode
Hodge--Dirac operator. -/
theorem fockJ_commutes_hodge_square :
    fockJ * (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac) =
      (embeddedSplitOctonionHodgeDirac * embeddedSplitOctonionHodgeDirac) * fockJ := by
  exact masterHestenesPhase_commutes_hodgeDirac_square

/-/ The finite two-sheet and five-mode axes are parallel square-minus-one
structures; this packet keeps their carriers distinct. -/
theorem two_sheet_and_fock_complex_axes_packet :
    emergentComplexK * emergentComplexK =
        -(1 : InfoGeometry.Canonical.TwoSheetComplexPolarization.SheetMat) ∧
    fockJ * fockJ = -(1 : FockMat) ∧
    fockJ * globalChirality 5 + globalChirality 5 * fockJ = 0 := by
  exact ⟨emergentComplexK_sq, fockJ_sq, fockJ_anticomm_chirality⟩

end InfoGeometry.Physics.QCDHestenesKreinFockPhaseBridge

end noncomputable section
