/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.FiniteGNSQuotientReconstruction

namespace InfoGeometry.OperatorAlgebra.FiniteGNSQuotientReconstruction
open GNSQuotientFinite

example : gnsClass nullExample = gnsClass 0 := nullExample_eq_zero_in_GNS

example : representation nullExample ≠ representation 0 := by
  intro h
  exact nullExample_ne_zero ((representation_eq_iff _ _).mp h)

example (v : V2C) :
    firstColumnEquiv (gnsClass (FiniteGNSConstruction.firstColumnMatrix v)) = v :=
  firstColumnEquiv.apply_symm_apply v

abbrev forwardWitness : Matrix (Fin 2) (Fin 2) ℂ := nullExample
noncomputable def reverseWitness : Matrix (Fin 2) (Fin 2) ℂ := star nullExample

theorem quotient_matrix_noncommuting :
    forwardWitness * reverseWitness ≠ reverseWitness * forwardWitness := by
  intro h
  have he := congrArg (fun M : M2C => M 0 0) h
  norm_num [forwardWitness, reverseWitness, nullExample, Matrix.mul_apply,
    Matrix.star_apply, Fin.sum_univ_two] at he

#print axioms firstColumnEquiv
#print axioms firstColumnEquiv_representation
#print axioms firstColumnEquiv_inner
#print axioms representation_entry_readback
#print axioms representation_eq_iff
#print axioms representation_injective
#print axioms quotient_matrix_noncommuting

end InfoGeometry.OperatorAlgebra.FiniteGNSQuotientReconstruction
