/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT

/-!
# Axiom Audit for GEMMidpointRotorBogoliubovQGT

Verifies via `#print axioms` that all exported theorems in
`InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT` depend exclusively
on Lean 4's foundational axioms (`propext`, `Quot.sound`, `Classical.choice`),
with zero `sorry`, `admit`, `native_decide`, or custom axioms.
-/

open InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT

#print axioms matrixE01_mul_E10_ne_mul_E10_E01_4
#print axioms InfoGeometry.OperatorAlgebra.PeirceSpine.symmetrically_split_midpoint_rotor_intertwining
#print axioms midpointRotor_normalized_sandwich
#print axioms InfoGeometry.OperatorAlgebra.PeirceSpine.kato_berry_spectral_flow_and_covariant_time
#print axioms kato_covariant_derivative_complement
#print axioms gemConnection_sq_split
#print axioms gemConnection_gamma0_parity
#print axioms bogoliubovRotor_mul_inv
#print axioms bogoliubovRotor_sandwich
#print axioms derivation_projector_off_diagonal
#print axioms derivationQGT_formula
#print axioms derivationQGT_skew_berry
