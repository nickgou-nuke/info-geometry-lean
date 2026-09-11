/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.ParaComplexTriadRealEmergenceBridge

/-!
# Audit: The Triad of The Holomorphic, The Antiholomorphic, and The Real

Direct axiom verification for all core theorems in `ParaComplexTriadRealEmergenceBridge`.
Requires standard Lean 4 foundation only: `propext`, `Classical.choice`, `Quot.sound`.
-/

open InfoGeometry.Canonical.ParaComplexTriadRealEmergence
open InfoGeometry.Canonical.ParaComplexTriadRealEmergence.ParaHermitianSpace
open InfoGeometry.Canonical.ParaComplexTriadRealEmergence.AntiChiralInvolution

#print axioms g_P_plus_P_plus_zero
#print axioms g_P_minus_P_minus_zero
#print axioms P_plus_add_P_minus
#print axioms P_plus_add_P_minus_eq_id
#print axioms g_eq_cross_terms
#print axioms sigma_comp_P_plus
#print axioms sigma_comp_P_minus
#print axioms real_state_chiral_conjugate
#print axioms real_spacetime_interval_emergence
#print axioms para_complex_triad_real_emergence_synthesis
#print axioms zorn_trace_zero
#print axioms zorn_det
#print axioms zorn_mass_shell_resonance
#print axioms zorn_massless_limit
#print axioms zorn_avoided_crossing_spectral_gap
#print axioms tomita_cone_identity
