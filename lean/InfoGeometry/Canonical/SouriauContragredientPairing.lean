import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Tactic

/-!
# Contragredient pairing for a linear symmetry

This file records the native linear-algebra core of the Souriau
adjoint/coadjoint square.  A linear equivalence acts on the dual by
pullback along its inverse, and the evaluation pairing is invariant.

No Lie-group, moment-map, topological, or standard-form structure is
introduced here; those are separate owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauContragredientPairing

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- Pullback by the inverse linear equivalence, i.e. the contragredient action. -/
def contragredient (e : V ≃ₗ[R] V) :
    Module.Dual R V →ₗ[R] Module.Dual R V where
  toFun μ := μ.comp e.symm.toLinearMap
  map_add' μ ν := by
    ext x
    simp
  map_smul' c μ := by
    ext x
    simp

@[simp] theorem contragredient_apply (e : V ≃ₗ[R] V)
    (μ : Module.Dual R V) (x : V) :
    contragredient e μ x = μ (e.symm x) := rfl

/-- The evaluation pairing is invariant under the adjoint/coadjoint pair. -/
theorem contragredient_pairing_invariant
    (e : V ≃ₗ[R] V) (μ : Module.Dual R V) (x : V) :
    contragredient e μ (e x) = μ x := by
  change μ (e.symm (e x)) = μ x
  simp

/-- Pullback reverses composition, as expected for the contragredient action. -/
theorem contragredient_trans
    (e f : V ≃ₗ[R] V) (μ : Module.Dual R V) :
    contragredient (e.trans f) μ =
      contragredient f (contragredient e μ) := by
  ext x
  simp [contragredient]

/-- The contragredient composition law as equality of linear maps. -/
theorem contragredient_trans_map
    (e f : V ≃ₗ[R] V) :
    contragredient (e.trans f) =
      (contragredient f).comp (contragredient e) := by
  ext μ x
  simp [contragredient]

/-- The contragredient action is itself a linear equivalence. -/
def contragredientLinearEquiv (e : V ≃ₗ[R] V) :
    Module.Dual R V ≃ₗ[R] Module.Dual R V where
  toLinearMap := contragredient e
  invFun := contragredient e.symm
  left_inv μ := by
    ext x
    simp [contragredient]
  right_inv μ := by
    ext x
    simp [contragredient]

@[simp] theorem contragredientLinearEquiv_apply
    (e : V ≃ₗ[R] V) (μ : Module.Dual R V) :
    contragredientLinearEquiv e μ = contragredient e μ := rfl

@[simp] theorem contragredientLinearEquiv_symm_apply
    (e : V ≃ₗ[R] V) (μ : Module.Dual R V) :
    (contragredientLinearEquiv e).symm μ = contragredient e.symm μ := by
  change contragredient e.symm μ = contragredient e.symm μ
  rfl

theorem contragredientLinearEquiv_pairing_invariant
    (e : V ≃ₗ[R] V) (μ : Module.Dual R V) (x : V) :
    contragredientLinearEquiv e μ (e x) = μ x := by
  exact contragredient_pairing_invariant e μ x

theorem contragredientLinearEquiv_trans_apply
    (e f : V ≃ₗ[R] V) (μ : Module.Dual R V) :
    contragredientLinearEquiv (e.trans f) μ =
      contragredientLinearEquiv f
        (contragredientLinearEquiv e μ) := by
  exact contragredient_trans e f μ

/-- The contragredient equivalence reverses the order of `LinearEquiv.trans`. -/
theorem contragredientLinearEquiv_trans (e f : V ≃ₗ[R] V) :
    contragredientLinearEquiv (e.trans f) =
      (contragredientLinearEquiv e).trans (contragredientLinearEquiv f) := by
  ext μ x
  simp [contragredientLinearEquiv, contragredient]

/-- The native general-linear contragredient representation. -/
def contragredientGeneralLinearRepresentation :
    LinearMap.GeneralLinearGroup R V →*
      LinearMap.GeneralLinearGroup R (Module.Dual R V) where
  toFun g := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (contragredientLinearEquiv
      (LinearMap.GeneralLinearGroup.toLinearEquiv g))
  map_one' := by
    have hone :
        contragredientLinearEquiv
            (LinearMap.GeneralLinearGroup.toLinearEquiv
              (1 : LinearMap.GeneralLinearGroup R V)) =
          (1 : Module.Dual R V ≃ₗ[R] Module.Dual R V) := by
      ext μ x
      change μ ((LinearMap.GeneralLinearGroup.toLinearEquiv
        (1 : LinearMap.GeneralLinearGroup R V)).symm x) = μ x
      rfl
    apply Units.ext
    exact congrArg LinearEquiv.toLinearMap hone
  map_mul' g h := by
    have hmul :
        contragredientLinearEquiv
            (LinearMap.GeneralLinearGroup.toLinearEquiv (g * h)) =
          contragredientLinearEquiv
              (LinearMap.GeneralLinearGroup.toLinearEquiv g) *
            contragredientLinearEquiv
              (LinearMap.GeneralLinearGroup.toLinearEquiv h) := by
      rw [LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
        LinearEquiv.mul_eq_trans]
      exact contragredientLinearEquiv_trans
        (LinearMap.GeneralLinearGroup.toLinearEquiv h)
        (LinearMap.GeneralLinearGroup.toLinearEquiv g)
    apply Units.ext
    exact congrArg LinearEquiv.toLinearMap hmul

@[simp] theorem contragredientGeneralLinearRepresentation_apply
    (g : LinearMap.GeneralLinearGroup R V) :
    contragredientGeneralLinearRepresentation g =
      LinearMap.GeneralLinearGroup.ofLinearEquiv
        (contragredientLinearEquiv
          (LinearMap.GeneralLinearGroup.toLinearEquiv g)) :=
  rfl

theorem contragredientGeneralLinearRepresentation_pairing_invariant
    (g : LinearMap.GeneralLinearGroup R V) (μ : Module.Dual R V) (x : V) :
    (contragredientGeneralLinearRepresentation g :
        Module.Dual R V →ₗ[R] Module.Dual R V) μ
        ((LinearMap.GeneralLinearGroup.toLinearEquiv g) x) = μ x := by
  change contragredientLinearEquiv
      (LinearMap.GeneralLinearGroup.toLinearEquiv g) μ
        ((LinearMap.GeneralLinearGroup.toLinearEquiv g) x) = μ x
  exact contragredientLinearEquiv_pairing_invariant
    (LinearMap.GeneralLinearGroup.toLinearEquiv g) μ x

/-- The inverse contragredient equivalence is induced by the inverse symmetry. -/
@[simp] theorem contragredientLinearEquiv_symm (e : V ≃ₗ[R] V) :
    (contragredientLinearEquiv e).symm =
      contragredientLinearEquiv e.symm := by
  ext μ x
  simp [contragredientLinearEquiv, contragredient]

@[simp] theorem contragredient_pairing_invariant_symm
    (e : V ≃ₗ[R] V) (μ : Module.Dual R V) (x : V) :
    contragredient e.symm μ x = μ (e x) := by
  simp [contragredient]

@[simp] theorem contragredient_symm_left
    (e : V ≃ₗ[R] V) (μ : Module.Dual R V) :
    contragredient e.symm (contragredient e μ) = μ := by
  ext x
  simp [contragredient]

@[simp] theorem contragredient_symm_right
    (e : V ≃ₗ[R] V) (μ : Module.Dual R V) :
    contragredient e (contragredient e.symm μ) = μ := by
  ext x
  simp [contragredient]

@[simp] theorem contragredient_id (μ : Module.Dual R V) :
    contragredient (LinearEquiv.refl R V) μ = μ := by
  ext x
  simp [contragredient]


end InfoGeometry.Canonical.SouriauContragredientPairing
