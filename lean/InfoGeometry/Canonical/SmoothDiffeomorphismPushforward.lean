/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SmoothDiffeomorphismDensityOrbit
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Fréchet pushforward of vector fields by smooth diffeomorphisms

The field carrier is the native real vector space `E → E`. The action uses
the derivative of the diffeomorphism at the inverse image of the evaluation
point. Smoothness of the field is not needed for the action laws. The action
is scoped so it cannot silently replace a pointwise action on functions.
-/

noncomputable section

namespace InfoGeometry.Canonical.SmoothDiffeomorphismPushforward

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual derivative pushforward of a vector field. -/
def pushforward (g : smoothDiffeomorphismSubgroup E) (X : E → E) (y : E) : E :=
  fderiv ℝ (g.val : E → E) (g.val.symm y) (X (g.val.symm y))

@[simp] theorem pushforward_one (X : E → E) :
    pushforward (1 : smoothDiffeomorphismSubgroup E) X = X := by
  funext y
  change fderiv ℝ id y (X y) = X y
  rw [fderiv_id]
  rfl

/-- The chain rule gives the action law in the same order as composition. -/
theorem pushforward_mul (g h : smoothDiffeomorphismSubgroup E) (X : E → E) :
    pushforward (g * h) X = pushforward g (pushforward h X) := by
  funext y
  change fderiv ℝ ((g.val : E → E) ∘ (h.val : E → E))
      (h.val.symm (g.val.symm y)) (X (h.val.symm (g.val.symm y))) =
    fderiv ℝ (g.val : E → E) (g.val.symm y)
      (fderiv ℝ (h.val : E → E) (h.val.symm (g.val.symm y))
        (X (h.val.symm (g.val.symm y))))
  rw [fderiv_comp (h.val.symm (g.val.symm y))
    ((g.property.1.differentiable (by simp)).differentiableAt)
    ((h.property.1.differentiable (by simp)).differentiableAt)]
  simp only [Homeomorph.apply_symm_apply, ContinuousLinearMap.comp_apply]

/-- Give the scoped derivative action priority over the generic action on
functions when an API asks only for `SMul`, as `MulAction.orbit` does. -/
scoped instance (priority := 1100) vectorFieldSMul :
    SMul (smoothDiffeomorphismSubgroup E) (E → E) := ⟨pushforward⟩

/-- Derivative pushforward is the chosen action only when this scope is open. -/
scoped instance vectorFieldAction :
    MulAction (smoothDiffeomorphismSubgroup E) (E → E) where
  smul := pushforward
  one_smul := pushforward_one
  mul_smul := pushforward_mul

@[simp] theorem vectorField_smul_eq_pushforward
    (g : smoothDiffeomorphismSubgroup E) (X : E → E) :
    g • X = pushforward g X := rfl

@[simp] theorem pushforward_zero (g : smoothDiffeomorphismSubgroup E) :
    pushforward g (0 : E → E) = 0 := by
  funext y
  exact map_zero _

theorem pushforward_add (g : smoothDiffeomorphismSubgroup E) (X Y : E → E) :
    pushforward g (X + Y) = pushforward g X + pushforward g Y := by
  funext y
  exact map_add _ _ _

theorem pushforward_smul (g : smoothDiffeomorphismSubgroup E) (c : ℝ) (X : E → E) :
    pushforward g (c • X) = c • pushforward g X := by
  funext y
  exact map_smul _ _ _

/-- The field action preserves the actual real linear structure. -/
def pushforwardLinearEquiv (g : smoothDiffeomorphismSubgroup E) :
    (E → E) ≃ₗ[ℝ] (E → E) where
  toFun := pushforward g
  invFun := pushforward g⁻¹
  left_inv X := by rw [← pushforward_mul, inv_mul_cancel, pushforward_one]
  right_inv X := by rw [← pushforward_mul, mul_inv_cancel, pushforward_one]
  map_add' := pushforward_add g
  map_smul' := pushforward_smul g

/-- Symmetries of a field use derivative pushforward, not pointwise action. -/
def vectorFieldSymmetrySubgroup (X : E → E) : Subgroup (smoothDiffeomorphismSubgroup E) :=
  MulAction.stabilizer (smoothDiffeomorphismSubgroup E) X

theorem mem_vectorFieldSymmetrySubgroup_iff (g : smoothDiffeomorphismSubgroup E)
    (X : E → E) :
    g ∈ vectorFieldSymmetrySubgroup X ↔ ∀ y, pushforward g X y = X y := by
  change pushforward g X = X ↔ _
  exact funext_iff

/-- Coordinate transfer conjugates the exact stabilizer subgroup. -/
theorem klein_abbildung_symmetry_conjugation
    (g : smoothDiffeomorphismSubgroup E) (X : E → E) :
    vectorFieldSymmetrySubgroup (pushforward g X) =
      (vectorFieldSymmetrySubgroup X).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g X

/-- The orbit is the homogeneous coset space of the field stabilizer. -/
def vectorFieldOrbitEquivQuotient (X : E → E) :
    MulAction.orbit (smoothDiffeomorphismSubgroup E) X ≃
      (smoothDiffeomorphismSubgroup E) ⧸ vectorFieldSymmetrySubgroup X :=
  MulAction.orbitEquivQuotientStabilizer (smoothDiffeomorphismSubgroup E) X

end InfoGeometry.Canonical.SmoothDiffeomorphismPushforward
