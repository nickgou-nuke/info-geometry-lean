/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarProductPositivity

/-! Axiom audit of core transport and full algebraic product positivity. -/
open InfoGeometry.OperatorAlgebra.CuntzComplexStarColimitEmbedding
open InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
open InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents

#print axioms coreMap
#print axioms coreMap_bijective
#print axioms coreEquiv
#print axioms coreEquiv_val
#print axioms coreRetraction
#print axioms quotientHom_coreRetraction
#print axioms coreRetraction_quotientHom
#print axioms coreRetraction_one
#print axioms coreRetraction_star
#print axioms component
#print axioms component_wordPair
#print axioms delta_component
#print axioms component_star
#print axioms projection_star_mul
#print axioms mem_core_of_degree_zero
#print axioms homogeneous_nat_square_nonneg
#print axioms homogeneous_neg_nat_square_nonneg
#print axioms homogeneous_square_nonneg
#print axioms quotientProductFunctional
#print axioms quotientProductFunctional_embed
#print axioms quotientProductFunctional_one
#print axioms quotientProductFunctional_star
#print axioms quotientProductFunctional_embed_nonneg
#print axioms quotientProductFunctional_core_nonneg
#print axioms coreRetraction_projection
#print axioms quotientProductFunctional_projection
#print axioms quotientProductFunctional_nonneg
