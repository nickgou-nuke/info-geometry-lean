/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import Mathlib.Tactic.Abel

/-!
# Variation of derivation-based noncommutative curvature

The existing curvature is a native Mathlib two-cochain. Its exact perturbation
formula retains both multiplication orders and the Lie-bracket term in the
base directions. The first variation is a linear map between the existing
native cochain spaces. The mixed quadratic term is symmetric in the two
one-form variations, although the coefficient multiplication need not commute.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra
open LieModule.Cohomology

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- The mixed commutator wedge of two operator-valued one-forms. -/
def connectionMixedWedge (Γ α : OneForm K) : TwoForm K :=
  ⟨LinearMap.mk₂ R
      (fun x y =>
        (Γ x * α y - α y * Γ x) - (Γ y * α x - α x * Γ y))
      (by
        intro x₁ x₂ y
        simp only [map_add, add_mul, mul_add]
        abel)
      (by
        intro r x y
        simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_sub])
      (by
        intro x y₁ y₂
        simp only [map_add, add_mul, mul_add]
        abel)
      (by
        intro r x y
        simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_sub]),
    by
      intro x
      exact sub_self _⟩

@[simp] theorem connectionMixedWedge_apply
    (Γ α : OneForm K) (x y : K.L) :
    connectionMixedWedge K Γ α x y =
      (Γ x * α y - α y * Γ x) - (Γ y * α x - α x * Γ y) :=
  rfl

/-- Symmetry comes from the two degree-one slots, not from commuting
coefficient matrices. -/
theorem connectionMixedWedge_comm (Γ α : OneForm K) :
    connectionMixedWedge K Γ α = connectionMixedWedge K α Γ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (Γ x * α y - α y * Γ x) - (Γ y * α x - α x * Γ y) =
    (α x * Γ y - Γ y * α x) - (α y * Γ x - Γ x * α y)
  abel

/-- On the diagonal the mixed wedge is twice the quadratic wedge. -/
theorem connectionMixedWedge_self (α : OneForm K) :
    connectionMixedWedge K α α = (2 : R) • connectionWedgeSquare K α := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (α x * α y - α y * α x) - (α y * α x - α x * α y) =
    (2 : R) • (α x * α y - α y * α x)
  rw [two_smul]
  abel

/-- The covariant exterior derivative on one-forms as a native linear map. -/
def covariantExteriorDerivativeOne (Γ : OneForm K) :
    OneForm K →ₗ[R] TwoForm K where
  toFun α := exteriorDerivativeOne K α + connectionMixedWedge K Γ α
  map_add' α β := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change exteriorDerivativeOne K (α + β) x y +
        connectionMixedWedge K Γ (α + β) x y =
      (exteriorDerivativeOne K α x y + connectionMixedWedge K Γ α x y) +
        (exteriorDerivativeOne K β x y + connectionMixedWedge K Γ β x y)
    simp only [exteriorDerivativeOne_apply, connectionMixedWedge_apply,
      LinearMap.add_apply, map_add, LieModule.Cohomology.add_apply_apply,
      mul_add, add_mul]
    abel
  map_smul' t α := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change exteriorDerivativeOne K (t • α) x y +
        connectionMixedWedge K Γ (t • α) x y =
      t • (exteriorDerivativeOne K α x y + connectionMixedWedge K Γ α x y)
    simp only [exteriorDerivativeOne_apply, connectionMixedWedge_apply,
      LinearMap.smul_apply, map_smul, LieModule.Cohomology.smul_apply_apply,
      smul_mul_assoc, mul_smul_comm,
      smul_add, smul_sub]

@[simp] theorem covariantExteriorDerivativeOne_apply
    (Γ α : OneForm K) (x y : K.L) :
    covariantExteriorDerivativeOne K Γ α x y =
      K.operatorAction x (α y) - K.operatorAction y (α x) - α ⁅x, y⁆ +
        ((Γ x * α y - α y * Γ x) - (Γ y * α x - α x * Γ y)) :=
  rfl

/-- Exact finite perturbation formula in the full noncommutative coefficient
algebra. No terms of order two are discarded. -/
theorem connectionCurvature_add_smul
    (Γ α : OneForm K) (t : R) :
    connectionCurvature K (Γ + t • α) =
      connectionCurvature K Γ +
        t • covariantExteriorDerivativeOne K Γ α +
        t ^ 2 • connectionWedgeSquare K α := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change connectionCurvature K (Γ + t • α) x y =
    connectionCurvature K Γ x y +
      t • covariantExteriorDerivativeOne K Γ α x y +
      t ^ 2 • connectionWedgeSquare K α x y
  simp only [connectionCurvature_apply, covariantExteriorDerivativeOne_apply,
    connectionWedgeSquare_apply, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_sub, smul_smul, pow_two]
  abel

/-- Unit-parameter form of the exact curvature perturbation identity. -/
theorem connectionCurvature_add (Γ α : OneForm K) :
    connectionCurvature K (Γ + α) =
      connectionCurvature K Γ + covariantExteriorDerivativeOne K Γ α +
        connectionWedgeSquare K α := by
  simpa using connectionCurvature_add_smul K Γ α (1 : R)

/-- Changing the connection changes its linearized curvature by the mixed
wedge term. -/
theorem covariantExteriorDerivativeOne_add_smul
    (Γ α β : OneForm K) (t : R) :
    covariantExteriorDerivativeOne K (Γ + t • α) β =
      covariantExteriorDerivativeOne K Γ β +
        t • connectionMixedWedge K α β := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change covariantExteriorDerivativeOne K (Γ + t • α) β x y =
    covariantExteriorDerivativeOne K Γ β x y +
      t • connectionMixedWedge K α β x y
  simp only [covariantExteriorDerivativeOne_apply, connectionMixedWedge_apply,
    LinearMap.add_apply, LinearMap.smul_apply, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

/-- The second mixed curvature difference is independent of the original
connection. -/
theorem connectionCurvature_mixed_difference (Γ α β : OneForm K) :
    connectionCurvature K (Γ + α + β) - connectionCurvature K (Γ + α) -
        connectionCurvature K (Γ + β) + connectionCurvature K Γ =
      connectionMixedWedge K α β := by
  have h := covariantExteriorDerivativeOne_add_smul K Γ α β (1 : R)
  simp only [one_smul] at h
  rw [connectionCurvature_add K (Γ + α) β, h,
    connectionCurvature_add K Γ β]
  abel

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
