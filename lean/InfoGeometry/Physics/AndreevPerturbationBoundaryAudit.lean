/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.AndreevPerturbationBoundary
open InfoGeometry.Physics.GeneralFermionicAndreevCarrier
#print axioms andreevRotation_mulVec_injective
#print axioms andreevRotation_perturbation_eq_iff

example (x : Fin 2 ⊕ Fin 2 → ℤ) :
    andreevRotation.mulVec (x + (fun _ => 1)) ≠ andreevRotation.mulVec x := by
  rw [andreevRotation_perturbation_eq_iff]
  intro h
  have he := congrFun h (Sum.inl 0)
  norm_num at he
