/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CayleyHestenesSectorKernels
import InfoGeometry.Canonical.CayleyHestenesWittGradedConcreteBridge

open InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge
open InfoGeometry.Canonical.CayleyHestenesWittGradedConcreteBridge
open InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge

#print axioms CayleyHestenesGradedDatum.KC_left_inverse
#print axioms CayleyHestenesGradedDatum.KC_injective
#print axioms CayleyHestenesGradedDatum.M_comm_KC
#print axioms CayleyHestenesGradedDatum.commutator_factor
#print axioms CayleyHestenesGradedDatum.anticommutator_factor
#print axioms CayleyHestenesGradedDatum.ker_commutator_eq_eigenspace_neg_one
#print axioms CayleyHestenesGradedDatum.ker_anticommutator_eq_eigenspace_one
#print axioms plain_intertwiner_range_le_minus_eigenspace
#print axioms plain_intertwiner_obstruction

example : wittGradedDatum.M.HasEigenvector 1 (Pi.single (0 : Fin 8) (1 : ℝ)) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · change longitudinalTransverseMat.mulVec (Pi.single (0 : Fin 8) (1 : ℝ)) =
      (1 : ℝ) • Pi.single (0 : Fin 8) (1 : ℝ)
    ext i
    fin_cases i <;>
      norm_num [longitudinalTransverseMat,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]
  · intro h
    have := congrFun h (0 : Fin 8)
    simp at this

example : wittGradedDatum.M.HasEigenvector (-1) (Pi.single (1 : Fin 8) (1 : ℝ)) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · change longitudinalTransverseMat.mulVec (Pi.single (1 : Fin 8) (1 : ℝ)) =
      (-1 : ℝ) • Pi.single (1 : Fin 8) (1 : ℝ)
    ext i
    fin_cases i <;>
      norm_num [longitudinalTransverseMat,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply]
  · intro h
    have := congrFun h (1 : Fin 8)
    simp at this

example : LinearMap.ker (wittGradedDatum.C * wittGradedDatum.K -
    wittGradedDatum.K * wittGradedDatum.C) = wittGradedDatum.M.eigenspace (-1) :=
  wittGradedDatum.ker_commutator_eq_eigenspace_neg_one

example : LinearMap.ker (wittGradedDatum.C * wittGradedDatum.K +
    wittGradedDatum.K * wittGradedDatum.C) = wittGradedDatum.M.eigenspace 1 :=
  wittGradedDatum.ker_anticommutator_eq_eigenspace_one
