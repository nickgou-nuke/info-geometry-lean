/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NoncommutativeZornBdGDerivations

/-!
# Audit: NoncommutativeZornBdGDerivationsAudit

Automated kernel verification of Noncommutative Operator Zorn Algebras:
- Verifies zero debt: 0 sorry, 0 admit, 0 custom axioms.
- Verifies Krein metric involution and self-adjointness.
- Verifies BdG squared off-diagonal commutator curvature: $(H^2)_{01} = D \Delta - \Delta D$.
- Verifies non-triviality of operator vector self-cross product $\mathbf{u} \times \mathbf{u} = [u_{i+1}, u_{i-1}]$.
- Verifies vanishing of self-cross product over commutative rings.
- Verifies exact subring isomorphism of single-color slice with $\operatorname{Mat}(2 \times 2, A)$.
- Verifies derivation annihilation of unity $D(1) = 0$.
- Verifies dynamic BdG pairing generation from Dirac mass seed $\mathbf{\Delta} = 2 D \mathbf{w}_1$.
- Axiom footprint check: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.NoncommutativeZornBdGDerivationsAudit

open Matrix
open InfoGeometry.Physics.NoncommutativeZornBdGDerivations

set_option linter.unusedVariables false

-- 1. Signature and Type-Level Verification
#check @kreinMetric_sq
#check @kreinMetric_star
#check @bdgHamiltonian_sq
#check @bdgHamiltonian_sq_off_diagonal_01
#check @crossNC_self_commutators
#check @crossNC_self_comm_ring
#check @embedMat2_mul
#check @embedMat2_injective
#check @embedMat2_mul_assoc
#check @embedMat2_bdg_square_curvature
#check @ncZorn_add_self_eq_self
#check @derivation_annihilates_one
#check @dynamic_pairing_from_dirac_mass
#check @reconstructedBdGZorn_components

-- 2. Axiom Footprint Verification
#print axioms kreinMetric_sq
#print axioms kreinMetric_star
#print axioms bdgHamiltonian_sq
#print axioms bdgHamiltonian_sq_off_diagonal_01
#print axioms crossNC_self_commutators
#print axioms crossNC_self_comm_ring
#print axioms embedMat2_mul
#print axioms embedMat2_injective
#print axioms embedMat2_mul_assoc
#print axioms embedMat2_bdg_square_curvature
#print axioms ncZorn_add_self_eq_self
#print axioms derivation_annihilates_one
#print axioms dynamic_pairing_from_dirac_mass
#print axioms reconstructedBdGZorn_components

end InfoGeometry.Physics.NoncommutativeZornBdGDerivationsAudit
