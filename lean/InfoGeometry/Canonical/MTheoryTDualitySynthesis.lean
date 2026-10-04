import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Canonical.Cl55WittChiralityRefinement
import InfoGeometry.Canonical.KantorFiveGradedTDualityBridge
import Mathlib.Tactic

noncomputable section
namespace InfoGeometry.Canonical.MTheoryTDualitySynthesis

open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Canonical.KantorFiveGradedTDuality

theorem cl55_gamma_is_involution : gammaChiral * gammaChiral = 1 :=
  gammaChiral_sq

theorem cl55_creation_off_diagonal (i : Fin 5) :
    creation i =
      peircePlus gammaChiral * creation i * peirceMinus gammaChiral +
      peirceMinus gammaChiral * creation i * peircePlus gammaChiral := by
  apply odd_off_diagonal_split gammaChiral (creation i) cl55_gamma_is_involution
  have h_anticomm := gammaChiral_e_anticomm i
  change gammaChiral * creation i = -(creation i * gammaChiral) at h_anticomm
  rw [h_anticomm, add_neg_cancel]

theorem cl55_annihilation_off_diagonal (i : Fin 5) :
    annihilation i =
      peircePlus gammaChiral * annihilation i * peirceMinus gammaChiral +
      peirceMinus gammaChiral * annihilation i * peircePlus gammaChiral := by
  apply odd_off_diagonal_split gammaChiral (annihilation i) cl55_gamma_is_involution
  have h_anticomm := gammaChiral_f_anticomm i
  change gammaChiral * annihilation i = -(annihilation i * gammaChiral) at h_anticomm
  rw [h_anticomm, add_neg_cancel]

end InfoGeometry.Canonical.MTheoryTDualitySynthesis
