import InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

/-!
# Compatibility of the two native `Cl(5,5)` Hodge operator APIs

The Clifford-layer envelope and the canonical Witt-spinor envelope expose the
same three-mode Hodge--Dirac matrix under different names.  This file records
that equality explicitly.  It does not identify their supercharge conventions:
those definitions use different mode combinations and therefore require a
separate comparison theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55MasterHodgeOperatorCompatibilityBridge

open InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

theorem hodgeDirac_eq_embeddedSplitOctonionHodgeDirac :
    _root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.hodgeDirac =
      embeddedSplitOctonionHodgeDirac := by
  dsimp [_root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.hodgeDirac,
    _root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.hodgeDiff,
    _root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.hodgeCodiff,
    _root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.eps,
    _root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.iota,
    embeddedSplitOctonionHodgeDirac, masterCreation, masterAnnihilation]
  abel

theorem hodgeDirac_sq_eq_three :
    _root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.hodgeDirac *
        _root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.hodgeDirac =
      (3 : ℝ) • (1 : _root_.InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge.Mat32) := by
  rw [hodgeDirac_eq_embeddedSplitOctonionHodgeDirac]
  exact embeddedSplitOctonionHodgeDirac_sq

end InfoGeometry.Canonical.Cl55MasterHodgeOperatorCompatibilityBridge
