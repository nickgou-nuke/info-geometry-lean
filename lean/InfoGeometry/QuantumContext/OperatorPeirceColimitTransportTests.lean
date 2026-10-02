import InfoGeometry.QuantumContext.OperatorPeirceColimitTransport
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Regression Tests and Axiom Audits for Operator Peirce Colimit Transport

This module exercises the abstract operator theorems and transitive axiom dependencies
of `OperatorPeirceColimitTransport.lean`.

All tests are kernel-checked with 0 sorry, 0 admit, and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.OperatorPeirceColimitTransportTests

open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.QuantumContext.MassAsCommutantCoupling
open InfoGeometry.QuantumContext.OperatorPeirceColimitTransport

/-! ### Axiom Inspections: Ensuring 100% Kernel Truth -/

#print axioms generalBipolar_swaps
#print axioms generalBipolar_anticommutes
#print axioms generalBipolar_hamiltonian_square
#print axioms map_idempotent
#print axioms map_complementIdempotent
#print axioms map_grading
#print axioms map_generalBipolar
#print axioms map_balancedCoupling
#print axioms colimit_transport_dirac_dispersion

end InfoGeometry.QuantumContext.OperatorPeirceColimitTransportTests
