/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.BostConnesClassFieldTheoryBridge

/-!
# Audit: Bost-Connes Explicit Class Field Theory and Galois Intertwining

Direct axiom verification for all core theorems in `BostConnesClassFieldTheoryBridge`.
Requires standard Lean 4 foundation only: `propext`, `Classical.choice`, `Quot.sound`.
-/

open InfoGeometry.Algebra.BostConnesClassFieldTheory.GaloisGroupAction

#print axioms galois_e_zero
#print axioms galois_e_add
#print axioms galois_e_star
#print axioms galois_covar_right
#print axioms galois_covar_left
#print axioms galois_P_invariance
#print axioms galois_e_one
#print axioms galois_e_mul
#print axioms galois_modular_comm_e
#print axioms galois_modular_comm_mu
#print axioms galois_modular_comm_P
#print axioms arithmetic_intertwining_law
#print axioms bost_connes_class_field_theory_synthesis
