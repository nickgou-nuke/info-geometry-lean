import InfoGeometry.Canonical.CartanInfinitesimalExponentialBridge
import InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry

/-!
# Native Cartan weights for the two-sheet Clifford generator

This file transports the already proved commutator readouts for the native
two-sheet Hamiltonian into the generic `IsCartanEigenOperator` interface.
It records only the infinitesimal weight statement.  No exponential flow,
ODE integration, positivity, or partition-function identity is inferred from
that statement.
-/

noncomputable section

namespace InfoGeometry.Canonical.CommonGeneratorCartanWeightBridge

open InfoGeometry.Canonical.CartanInfinitesimalExponentialBridge
open InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
open InfoGeometry.Clifford.ChiralLorentzCARLift
open InfoGeometry.Clifford.ChiralLorentzFockQuadratic
open InfoGeometry.Clifford.Cl44Witt

theorem freeSheetHamiltonian_creation_plus_isCartanEigenOperator
    (Eplus Eminus : ℝ) :
    IsCartanEigenOperator (freeSheetHamiltonian Eplus Eminus) (adag 0) Eplus := by
  exact freeSheetHamiltonian_commutator_creation_plus Eplus Eminus

theorem freeSheetHamiltonian_creation_minus_isCartanEigenOperator
    (Eplus Eminus : ℝ) :
    IsCartanEigenOperator (freeSheetHamiltonian Eplus Eminus) (adag 1) Eminus := by
  exact freeSheetHamiltonian_commutator_creation_minus Eplus Eminus

theorem freeSheetHamiltonian_annihilation_plus_isCartanEigenOperator
    (Eplus Eminus : ℝ) :
    IsCartanEigenOperator (freeSheetHamiltonian Eplus Eminus) (a 0) (-Eplus) := by
  change algebraCommutator (freeSheetHamiltonian Eplus Eminus) (a 0) =
    (-Eplus) • a 0
  simpa only [neg_smul] using
    (freeSheetHamiltonian_commutator_annihilation_plus Eplus Eminus)

theorem freeSheetHamiltonian_annihilation_minus_isCartanEigenOperator
    (Eplus Eminus : ℝ) :
    IsCartanEigenOperator (freeSheetHamiltonian Eplus Eminus) (a 1) (-Eminus) := by
  change algebraCommutator (freeSheetHamiltonian Eplus Eminus) (a 1) =
    (-Eminus) • a 1
  simpa only [neg_smul] using
    (freeSheetHamiltonian_commutator_annihilation_minus Eplus Eminus)

end InfoGeometry.Canonical.CommonGeneratorCartanWeightBridge
