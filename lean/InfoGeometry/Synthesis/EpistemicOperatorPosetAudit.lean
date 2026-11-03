/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.EpistemicOperatorPoset

/-!
# Axiom-Footprint Audit for `InfoGeometry.Synthesis.EpistemicOperatorPoset`

Verifies that every public definition, lemma, and master synthesis theorem in
`InfoGeometry.Synthesis.EpistemicOperatorPoset` depends exclusively on standard
Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero custom
axioms, zero wrappers, and zero sorry.
-/

namespace InfoGeometry.Synthesis.EpistemicOperatorPosetAudit

open InfoGeometry.Synthesis.EpistemicOperatorPoset

#print axioms stageRank
#print axioms stageRank_injective
#print axioms epistemic_causal_poset_dag_acyclic
#print axioms comm
#print axioms anticomm
#print axioms comm_skew
#print axioms anticomm_symm
#print axioms comm_anticomm_reconstruction
#print axioms anticomm_sub_comm
#print axioms jacobi_identity
#print axioms leibniz_derivation_left
#print axioms leibniz_derivation_right
#print axioms compIdempotent
#print axioms parityAdjoint
#print axioms idempotent_complement_laws
#print axioms parity_involution
#print axioms parity_conjugation_P
#print axioms parity_conjugation_comp
#print axioms peirce11
#print axioms peirce10
#print axioms peirce01
#print axioms peirce00
#print axioms peirce_quartet_reconstruction
#print axioms peirce_orthogonality
#print axioms peirce_diagonal_idempotents
#print axioms conePlus
#print axioms coneMinus
#print axioms nilpotent_cones
#print axioms cone_corner_products
#print axioms genPhi
#print axioms genJ
#print axioms genV
#print axioms genSig
#print axioms tetraktys_split_quaternion_algebra
#print axioms tetraktys_sigma_squared
#print axioms defect
#print axioms defect_idempotent
#print axioms defect_perturbed_idempotent
#print axioms defect_completed_square
#print axioms unipotentPlus
#print axioms unipotentPlusInv
#print axioms unipotentMinus
#print axioms unipotentMinusInv
#print axioms unipotent_shear_inverses
#print axioms unipotent_shear_conjugations
#print axioms peirceCorner
#print axioms peirceCorner_product_resolution
#print axioms peirceCorner_injective
#print axioms master_epistemic_operator_synthesis

end InfoGeometry.Synthesis.EpistemicOperatorPosetAudit
