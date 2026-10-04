import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Canonical.Cl55WittChiralityRefinement
import InfoGeometry.Canonical.KantorFiveGradedTDualityBridge
import Mathlib.Tactic

/-!
# Chiral block decomposition in the concrete stage-five matrix model

This module specializes the generic Peirce off-diagonal decomposition to the
existing `MatStage 5` chirality operator and its creation/annihilation
generators.  The Kantor/T-duality import supplies the generic involution lemma
used in the proof; this file does not construct a Kantor-pair structure on
`MatStage 5`, a five-graded Lie algebra representation, a T-duality action, or
an M-theory model.
-/

noncomputable section
namespace InfoGeometry.Canonical.MTheoryTDualitySynthesis

open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Canonical.KantorFiveGradedTDuality

theorem cl55_creation_off_diagonal (i : Fin 5) :
    creation i =
      peircePlus gammaChiral * creation i * peirceMinus gammaChiral +
      peirceMinus gammaChiral * creation i * peircePlus gammaChiral := by
  apply odd_off_diagonal_split gammaChiral (creation i) gammaChiral_sq
  have h_anticomm := gammaChiral_e_anticomm i
  change gammaChiral * creation i = -(creation i * gammaChiral) at h_anticomm
  rw [h_anticomm, add_neg_cancel]

theorem cl55_annihilation_off_diagonal (i : Fin 5) :
    annihilation i =
      peircePlus gammaChiral * annihilation i * peirceMinus gammaChiral +
      peirceMinus gammaChiral * annihilation i * peircePlus gammaChiral := by
  apply odd_off_diagonal_split gammaChiral (annihilation i) gammaChiral_sq
  have h_anticomm := gammaChiral_f_anticomm i
  change gammaChiral * annihilation i = -(annihilation i * gammaChiral) at h_anticomm
  rw [h_anticomm, add_neg_cancel]

end InfoGeometry.Canonical.MTheoryTDualitySynthesis
