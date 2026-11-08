/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearAlgebraicResolventObstruction
import InfoGeometry.Physics.NuclearComplementaryResolvent

/-! Kernel dependencies of the algebraic obstruction and the conditional
complementary-space replacement. No inverse existence on all formal sequences
is asserted by the replacement. -/

open InfoGeometry.Physics.NuclearAlgebraicResolventObstruction
open InfoGeometry.Physics.NuclearComplementaryResolvent

#print axioms discardedEigenvector_ne_zero
#print axioms fullHamiltonian_discardedEigenvector
#print axioms no_left_complementary_resolvent
#print axioms denominator_mul_liftInverse
#print axioms liftInverse_mul_denominator
#print axioms eigen_equation_iff_of_equiv
#print axioms reconstruct_eigenvector_of_equiv
