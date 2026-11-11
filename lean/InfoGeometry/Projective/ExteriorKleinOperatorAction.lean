/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.ExteriorKleinProjective

/-!
# The native exterior-square action on Klein bivectors

An arbitrary real endomorphism of `Vec4` acts by Mathlib's `exteriorPower.map`.
The established exterior/bivector equivalence transports this action to the
repository's six-coordinate carrier. Composition retains its original order.
The resulting assignment is multiplicative; it is not an additive or Lie
algebra representation in the endomorphism argument.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinOperatorAction

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.ExteriorKleinProjective

/-- The actual exterior-square action, expressed in native bivector coordinates. -/
def bivectorAction (A : Module.End ℝ Vec4) : Module.End ℝ Bivector4 :=
  exteriorBivectorLinearEquiv.toLinearMap.comp
    ((exteriorPower.map 2 A).comp exteriorBivectorLinearEquiv.symm.toLinearMap)

theorem exteriorMap_pair (A : Module.End ℝ Vec4) (u v : Vec4) :
    exteriorPower.map 2 A (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      exteriorPower.ιMulti ℝ 2 ![A u, A v] := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The coordinate equivalence intertwines the constructed action with `Λ² A`. -/
theorem bivectorAction_intertwines (A : Module.End ℝ Vec4) (X : ExteriorSquare) :
    bivectorAction A (exteriorBivectorLinearEquiv X) =
      exteriorBivectorLinearEquiv (exteriorPower.map 2 A X) := by
  simp [bivectorAction]

theorem bivectorAction_wedge (A : Module.End ℝ Vec4) (u v : Vec4) :
    bivectorAction A (wedgeVec4 u v) = wedgeVec4 (A u) (A v) := by
  rw [← exteriorBivectorLinearEquiv_ιMulti, bivectorAction_intertwines,
    exteriorMap_pair, exteriorBivectorLinearEquiv_ιMulti]

theorem bivectorAction_id :
    bivectorAction (LinearMap.id : Module.End ℝ Vec4) = LinearMap.id := by
  apply LinearMap.ext
  intro P
  simp [bivectorAction]

/-- Ordered composition is preserved without a commutativity hypothesis. -/
theorem bivectorAction_comp (A B : Module.End ℝ Vec4) :
    bivectorAction (A.comp B) = (bivectorAction A).comp (bivectorAction B) := by
  apply LinearMap.ext
  intro P
  simp [bivectorAction, exteriorPower.map_comp]

/-- The exterior square is a representation of the endomorphism monoid. -/
def bivectorActionMonoidHom : Module.End ℝ Vec4 →* Module.End ℝ Bivector4 where
  toFun := bivectorAction
  map_one' := bivectorAction_id
  map_mul' A B := bivectorAction_comp A B

/-- An injective four-vector map acts injectively on bivectors. This statement
does not assert faithfulness of the assignment `A ↦ Λ² A`. -/
theorem bivectorAction_injective (A : Module.End ℝ Vec4)
    (hA : Function.Injective A) : Function.Injective (bivectorAction A) := by
  exact exteriorBivectorLinearEquiv.injective.comp
    ((exteriorPower.map_injective_field (n := 2) hA).comp
      exteriorBivectorLinearEquiv.symm.injective)

/-- An invertible four-vector action induces an equivalence with its actual
inverse acting on the exterior square. -/
def bivectorEquiv (A : Vec4 ≃ₗ[ℝ] Vec4) : Bivector4 ≃ₗ[ℝ] Bivector4 where
  toLinearMap := bivectorAction A.toLinearMap
  invFun := bivectorAction A.symm.toLinearMap
  left_inv P := by
    have hA : A.symm.toLinearMap.comp A.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact A.symm_apply_apply v
    have h := congrArg (fun T : Module.End ℝ Bivector4 => T P)
      (bivectorAction_comp A.symm.toLinearMap A.toLinearMap)
    rw [hA, bivectorAction_id] at h
    exact h.symm
  right_inv P := by
    have hA : A.toLinearMap.comp A.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact A.apply_symm_apply v
    have h := congrArg (fun T : Module.End ℝ Bivector4 => T P)
      (bivectorAction_comp A.toLinearMap A.symm.toLinearMap)
    rw [hA, bivectorAction_id] at h
    exact h.symm

@[simp] theorem bivectorEquiv_apply (A : Vec4 ≃ₗ[ℝ] Vec4) (P : Bivector4) :
    bivectorEquiv A P = bivectorAction A.toLinearMap P := rfl

end InfoGeometry.Projective.ExteriorKleinOperatorAction
