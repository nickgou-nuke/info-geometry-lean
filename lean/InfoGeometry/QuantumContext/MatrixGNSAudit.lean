/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.QuantumContext.MatrixGNS

/-!
# Audit Companion: Matrix GNS Representation and Tomita Modular Theory

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.QuantumContext.MatrixGNS`.
-/

open InfoGeometry.QuantumContext.MatrixGNS

#print axioms gnsInner_self_diagonal
#print axioms gnsInner_self_nonneg
#print axioms gnsLeftIdeal_diagonal_iff
#print axioms gnsLeftIdeal_mul_left
#print axioms gnsLeftIdeal_faithful
#print axioms gns_expectation_reproduction
#print axioms gns_cyclic_vector_separating
#print axioms rhoHalfInv_mul_rhoHalf
#print axioms rhoHalf_mul_rhoHalfInv
#print axioms tomitaJ_involutive
#print axioms tomitaJ_mul
#print axioms rhoHalf_mul_rhoHalf
#print axioms rhoHalfInv_mul_rhoHalfInv
#print axioms tomita_duality
#print axioms compile_matrix_gns
