/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis

/-!
# Axiom Audit for `ParaKahlerSouriauMassieuMajoranaSynthesis`
-/

namespace InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesisAudit

open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis

#check @paraComplexEndJ
#check @paraKahlerNeutralMetric
#check @paraKahlerCompatibility_and_involution
#check @paraKahlerMixedVariation
#check @paraKahlerGaugeShift
#check @bregmanParaKahlerPotential
#check @paraKahlerMixedVariation_gauge_invariant_and_bregman_pairing
#check @majoranaCrossPairing
#check @majoranaKreinInterval
#check @majorana_kleinQuadric_projective_ray_invariance
#check @gibbsPartitionSum
#check @souriauMassieuPotential
#check @souriauAttentionWeight
#check @gibbsPartitionSum_pos
#check @souriauAttentionWeight_pos
#check @massieu_free_entropy_legendre_identity
#check @souriauMassieu_shift_and_attention_scale_invariance
#check @souriauMomentMap
#check @fisherSouriauHessian
#check @hasDerivAt_gibbsPartitionSum_coord
#check @hasDerivAt_souriauMassieuPotential_coord
#check @hasDerivAt_souriauAttentionWeight_diag
#check @fisherSouriau_quadratic_eq_variance_and_nonneg

#print axioms paraKahlerCompatibility_and_involution
#print axioms paraKahlerMixedVariation_gauge_invariant_and_bregman_pairing
#print axioms majorana_kleinQuadric_projective_ray_invariance
#print axioms gibbsPartitionSum_pos
#print axioms souriauAttentionWeight_pos
#print axioms massieu_free_entropy_legendre_identity
#print axioms souriauMassieu_shift_and_attention_scale_invariance
#print axioms hasDerivAt_gibbsPartitionSum_coord
#print axioms hasDerivAt_souriauMassieuPotential_coord
#print axioms hasDerivAt_souriauAttentionWeight_diag
#print axioms fisherSouriau_quadratic_eq_variance_and_nonneg

end InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesisAudit
