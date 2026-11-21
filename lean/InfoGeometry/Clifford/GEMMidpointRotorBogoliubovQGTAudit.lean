/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT

/-!
# Axiom Audit for GEMMidpointRotorBogoliubovQGT

Verifies via `#print axioms` that all exported acceptance theorems, T16/T17
witnesses, and helper theorems in
`InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT` depend exclusively on
Lean 4's foundational axioms (`propext`, `Quot.sound`, `Classical.choice`),
with zero `sorry`, `admit`, `native_decide`, or custom axioms.
-/

open InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT

-- T16/T17 noncommutativity witnesses
#print axioms matrixE01_mul_E10_ne_mul_E10_E01_4
#print axioms mat4C_dirac_gamma_noncommutative_witness

-- Group 1: Midpoint Rotor
#print axioms unnormMidpointRotor_intertwining
#print axioms midpointRotor_normalized_sandwich
#print axioms midpointRotorRev_mul_midpointRotor

-- Group 2: Kato Peirce Corners & Covariant Annihilation
#print axioms InfoGeometry.OperatorAlgebra.PeirceSpine.kato_berry_spectral_flow_and_covariant_time
#print axioms kato_peirce_corner_and_covariant_annihilation
#print axioms kato_covariant_derivative_complement
#print axioms kato_derivation_covariant_annihilation

-- Group 3: GEM (1,3) Split & Lense–Thirring
#print axioms gemConnection_sq_split
#print axioms gemConnection_gamma0_parity
#print axioms gemConnection_sta_pseudoscalar_contrast
#print axioms gemConnection_sq_split_and_lenseThirring_rate

-- Group 4: Bogoliubov Rotor & Peirce Aporia
#print axioms bogoliubovRotor_neg_eq_inv
#print axioms bogoliubovRotor_mul_inv
#print axioms bogoliubovRotor_sandwich
#print axioms boostedFrame_sq
#print axioms bogoliubovRotor_ccr_norm
#print axioms bogoliubovRotor_eq_midpointRotor_and_sandwich
#print axioms bogoliubovRotor_peirce_aporia_neg_sinhSq

-- Group 5: Covariant QGT via DerivationLieLane
#print axioms derivation_projector_off_diagonal
#print axioms derivation_complement_off_diagonal
#print axioms derivationQGT_formula
#print axioms derivationQGT_skew_berry
#print axioms derivationQGT_leibniz_offDiagonal_and_berry_split
