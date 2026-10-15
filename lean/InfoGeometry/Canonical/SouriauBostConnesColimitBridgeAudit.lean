/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauBostConnesColimitBridge

/-!
# Audit Companion: Souriau-Bost-Connes Colimit Bridge

Independent formal verification and axiom audit for the Souriau-Bost-Connes
reciprocal partition and Cuntz defect elimination colimit bridge.
-/

open InfoGeometry.Canonical.SouriauBostConnesColimitBridge

#print axioms prime_ge_two
#print axioms real_prime_gt_one
#print axioms log_prime_pos
#print axioms boltzmannRootVariable_lt_one
#print axioms one_sub_boltzmann_pos
#print axioms one_sub_boltzmann_ne_zero
#print axioms evaluatedWeylDenominator_ne_zero
#print axioms evaluatedWeylDenominator_pos
#print axioms evaluatedWeylDenominator_mul_finitePrimonPartition_eq_one
#print axioms finitePrimonPartition_mul_evaluatedWeylDenominator_eq_one
#print axioms cuntz_defect_elimination_ring
#print axioms cuntz_defect_elimination_module
#print axioms cuntz_vector_partition_of_unity
#print axioms cuntz_vector_range_reconstruction
#print axioms cuntz_defect_kernels_disjoint
#print axioms scalar_commutes_linearMap
#print axioms weyl_normalization_reciprocal_state
#print axioms souriau_bost_connes_colimit_bridge_verified
