/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification

/-!
# Audit of $\mathrm{Cl}(5,5)$ Five-Graded Duality, Para-Kähler Split Envelope, and Souriau Equivariance

Verifies the exported signatures and axiom footprints of
`InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification`.
-/

namespace InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnificationAudit

open InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification

#check @paraKahler_sum_quadratic_eq_two_pairing
#check @paraKahler_split_envelope_and_isotropic_vacuum_duality
#check @IsConformalFiveGradePreserving
#check @IsGradeReversalIntertwined
#check @gradeReversal_colimit_full_channel_intertwining
#check @souriauPartition_perm_invariant
#check @souriauMassieuPotential_perm_invariant
#check @gibbsProb_perm_equivariant
#check @fisherSouriauLaplacian_perm_equivariant

#print axioms paraKahler_sum_quadratic_eq_two_pairing
#print axioms paraKahler_split_envelope_and_isotropic_vacuum_duality
#print axioms gradeReversal_colimit_full_channel_intertwining
#print axioms souriauPartition_perm_invariant
#print axioms souriauMassieuPotential_perm_invariant
#print axioms gibbsProb_perm_equivariant
#print axioms fisherSouriauLaplacian_perm_equivariant

end InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnificationAudit
