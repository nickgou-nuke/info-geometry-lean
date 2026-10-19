/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.FisherSouriauGroupInversePermutation

/-!
# Axiom audit for permutation naturality of the Fisher--Souriau group inverse
-/

namespace InfoGeometry.Synthesis.FisherSouriauGroupInversePermutationAudit

open InfoGeometry.Synthesis.FisherSouriauGroupInversePermutation

#check @arithmeticMean_comp_perm
#check @centerScores_comp_perm
#check @reciprocalAttentionWeights_comp_perm
#check @fisherHessianGroupInverseCandidate_perm_equivariant
#check @scorePermutation
#check @fisherHessianEnd_linear_intertwines_perm
#check @fisherHessianGroupInverseCandidate_linear_intertwines_perm
#check @fisherHessianDrazinInverse_linear_intertwines_perm
#check @fisherHessianGroupInverse_energy_perm_invariant

#print axioms arithmeticMean_comp_perm
#print axioms centerScores_comp_perm
#print axioms reciprocalAttentionWeights_comp_perm
#print axioms fisherHessianGroupInverseCandidate_perm_equivariant
#print axioms fisherHessianEnd_linear_intertwines_perm
#print axioms fisherHessianGroupInverseCandidate_linear_intertwines_perm
#print axioms fisherHessianDrazinInverse_linear_intertwines_perm
#print axioms fisherHessianGroupInverse_energy_perm_invariant

end InfoGeometry.Synthesis.FisherSouriauGroupInversePermutationAudit
