/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-!
# Audit: Section 115 — Peirce–DeWitt Decomposition, Supercolor Symmetry, and Quantized Zorn Matrices

Independent audit verifying that:
1. All theorems in `InfoGeometry.Superalgebra.PeirceDeWittZornQuantization` compile cleanly.
2. Every theorem depends strictly on standard Core Lean 4 / Mathlib axioms:
   `[propext, Classical.choice, Quot.sound]`.
3. Zero `sorry`, zero `admit`, and zero custom axioms are introduced.
-/

namespace InfoGeometry.Superalgebra.PeirceDeWittZornAudit

open InfoGeometry.Superalgebra.PeirceDeWittZorn

/- Verification 1: Supercolor vector space & Baryon determinant identities. -/
#print axioms ColorVec3.dot_comm
#print axioms ColorVec3.cross_anticomm
#print axioms ColorVec3.baryonDet_antisymm_12
#print axioms ColorVec3.baryonDet_cyclic
#print axioms ColorVec3.baryonDet_red_green_blue

/- Verification 2: Peirce idempotents & Peirce–DeWitt completeness. -/
#print axioms ZornAlgebra.e₁_idempotent
#print axioms ZornAlgebra.e₂_idempotent
#print axioms ZornAlgebra.e₁_mul_e₂_zero
#print axioms ZornAlgebra.e₂_mul_e₁_zero
#print axioms ZornAlgebra.peirce_partition_of_unity
#print axioms ZornAlgebra.peirce_dewitt_completeness

/- Verification 3: Canonical CAR quantization & Pauli exclusion. -/
#print axioms ZornAlgebra.quark_mul_antiquark
#print axioms ZornAlgebra.antiquark_mul_quark
#print axioms ZornAlgebra.zorn_car_quantization_exact
#print axioms ZornAlgebra.quark_pauli_exclusion
#print axioms ZornAlgebra.antiquark_pauli_exclusion
#print axioms ZornAlgebra.quark_antiquark_noncomm

/- Verification 4: Supercolor diquark fusion & Baryon singlet closure. -/
#print axioms ZornAlgebra.supercolor_diquark_fusion
#print axioms ZornAlgebra.supercolor_antidiquark_fusion
#print axioms ZornAlgebra.supercolor_baryon_singlet_closure
#print axioms ZornAlgebra.rgb_baryon_vertex_is_unit

/- Verification 5: Canonical bridge to ZornVectorMatrix. -/
#print axioms colorVec3EquivZornVec3_dot
#print axioms colorVec3EquivZornVec3_cross
#print axioms zornAlgebraEquiv_peirce_idempotents
#print axioms zornAlgebraEquiv_mul

end InfoGeometry.Superalgebra.PeirceDeWittZornAudit
