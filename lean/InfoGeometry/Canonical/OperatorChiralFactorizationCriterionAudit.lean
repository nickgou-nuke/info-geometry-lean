/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorChiralFactorizationCriterion

namespace InfoGeometry.Canonical.OperatorChiralDeterminantDefect

-- Cancellation works even when the diagonal entries do not commute.
example (p m : Matrix (Fin 2) (Fin 2) ℤ) :
    chiralBlock p m p m * chiralAdjugate p m p m =
      scalarChiralBlock (leftQuadraticReadout p m p m) := by
  apply (chiralBlock_mul_adjugate_eq_scalar_iff p m p m).mpr
  exact ⟨Commute.refl p, Commute.refl m, rfl⟩

example : ¬ Commute (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ)
    !![0, 0; 1, 0] := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h.eq
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at he

-- An uncancelled diagonal commutator obstructs scalar factorization.
example :
    chiralBlock (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) !![0, 0; 1, 0] 0 0 *
      chiralAdjugate !![0, 1; 0, 0] !![0, 0; 1, 0] 0 0 ≠
      scalarChiralBlock (leftQuadraticReadout !![0, 1; 0, 0] !![0, 0; 1, 0] 0 0) := by
  intro h
  have hc := (chiralBlock_mul_adjugate_eq_scalar_iff _ _ _ _).mp h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hc.2.2
  norm_num [operatorCommutator, Matrix.mul_apply, Fin.sum_univ_two] at he

#print axioms chiralBlock_mul_adjugate_eq_scalar_iff
#print axioms operatorZorn_scalar_factorization_iff
#print axioms chiralBlock_mul_adjugate

end InfoGeometry.Canonical.OperatorChiralDeterminantDefect
