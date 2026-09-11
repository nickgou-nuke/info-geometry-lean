/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.BostConnesModularAutomorphismBridge

/-!
# Audit: Bost-Connes 1-Parameter Modular Automorphism Group and Range Invariance

Direct axiom verification for all core theorems in `BostConnesModularAutomorphismBridge`.
Requires standard Lean 4 foundation only: `propext`, `Classical.choice`, `Quot.sound`.
-/

open InfoGeometry.Algebra.BostConnesModularAutomorphism.ModularPhaseFlow

#print axioms star_central
#print axioms unitary_right
#print axioms sigma_mu_one
#print axioms sigma_mu_mul
#print axioms sigma_mu_isometry
#print axioms sigma_cov_right
#print axioms sigma_cov_left
#print axioms sigma_hecke_coprime
#print axioms sigma_P_invariance
#print axioms sigma_zero_mu
#print axioms sigma_add_mu
#print axioms sigma_inverse_mu
#print axioms bost_connes_modular_automorphism_synthesis
