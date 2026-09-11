import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SuperchargeTransportBridge

/-!
# Hestenes--Krein supercharge translation lane

This is the algebraic capstone for the finite/Krein side.  It records the
primitive zero-mode CAR/CCR closure and the transported quasilattice
translation derivative.  No analytic completion or manifold claim is made.
-/

namespace InfoGeometry.Canonical.HestenesKreinColimitSuperchargeTranslation

open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.SuperchargeTransportBridge
open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.BogoliubovTransport

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem primitive_zero_mode_superalgebra :
    CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E)) = 0 ∧
    CCRBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E)) =
      (2 : ℝ) • cptSuperchargeOp (E := E) := by
  exact ⟨parity_modular_supercharge_car_zero (E := E),
    parity_modular_supercharge_ccrBracket_eq_two_cpt (E := E)⟩

theorem primitive_zero_mode_chiral_flip
    {v : DoubledSpace E} (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (cptSuperchargeOp (E := E) v) :=
  cptSuperchargeOp_maps_plus_to_minus (E := E) hv

theorem quasilattice_translation_derivative_split
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) :
    quasilatticeTranslationCandidate (E := E) V =
      quasilatticePhaseLinearTranslationSeed (E := E) V +
        quasilatticePhaseAntilinearTranslationSeed (E := E) V :=
  quasilatticeTranslationCandidate_eq_phaseLinearSeed_add_phaseAntilinearSeed
    (E := E) V

theorem quasilattice_translation_antilinear_of_linear_commute
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (modular_j (E := E))
        (phaseLinearPart V.connectionGenerator)) :
    quasilatticeTranslationCandidate (E := E) V =
      quasilatticePhaseAntilinearTranslationSeed (E := E) V :=
  quasilatticeTranslationCandidate_eq_phaseAntilinearSeed_of_commute_phaseLinearPart
    (E := E) V hComm

end Core

end InfoGeometry.Canonical.HestenesKreinColimitSuperchargeTranslation
