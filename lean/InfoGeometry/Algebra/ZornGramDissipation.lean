/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornQuaternionProjectedGram

/-!
# Covector-to-vector operators of the real Zorn Gram forms

A bilinear form has type `Z →ₗ Z*`, whereas the dissipative operator used by
GENERIC has type `Z* →ₗ Z`. This file constructs the missing identification
from the existing positive coefficient pairing and its actual finite basis.
It does not silently treat the split multiplicative norm as positive.

For a form `B`, the operator is `e⁻¹ ∘ B ∘ e⁻¹`, where `e` is the constructed
coefficient-pairing dual equivalence. Symmetry, positivity, and the exact
ambient/quaternion kernels are transported through its evaluation identity.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornGramDissipation

open ZornPinorReconstruction ZornCARAdjoint ZornAssociatorGram
open ZornQuaternionProjectedGram
open InfoGeometry.Canonical.GunaydinGursey

local instance : FiniteDimensional ℝ Z :=
  (signedBasis (R := ℝ)).finiteDimensional_of_finite

theorem coefficientPairing_nondegenerate : coefficientPairing.Nondegenerate := by
  constructor
  · intro X hX
    exact (coefficientPairing_zero_iff X).mp (hX X)
  · intro X hX
    exact (coefficientPairing_zero_iff X).mp (hX X)

/-- Native linear duality constructed from the positive coefficient pairing. -/
def coefficientDuality : Z ≃ₗ[ℝ] Module.Dual ℝ Z :=
  coefficientPairing.toDual coefficientPairing_nondegenerate

@[simp] theorem coefficientDuality_apply (X Y : Z) :
    coefficientDuality X Y = coefficientPairing X Y := rfl

@[simp] theorem coefficientDuality_symm_pairing (φ : Module.Dual ℝ Z) (X : Z) :
    coefficientPairing (coefficientDuality.symm φ) X = φ X := by
  change coefficientDuality (coefficientDuality.symm φ) X = φ X
  rw [LinearEquiv.apply_symm_apply]

/-- The two uses of the inverse duality make both variance changes explicit. -/
def gramCovectorOperator (B : LinearMap.BilinForm ℝ Z) :
    Module.Dual ℝ Z →ₗ[ℝ] Z :=
  coefficientDuality.symm.toLinearMap.comp
    (B.comp coefficientDuality.symm.toLinearMap)

theorem gramCovectorOperator_eval (B : LinearMap.BilinForm ℝ Z)
    (φ ψ : Module.Dual ℝ Z) :
    φ (gramCovectorOperator B ψ) =
      B (coefficientDuality.symm ψ) (coefficientDuality.symm φ) := by
  change φ (coefficientDuality.symm (B (coefficientDuality.symm ψ))) = _
  rw [← coefficientDuality_symm_pairing φ,
    coefficientPairing_symm, coefficientDuality_symm_pairing]

theorem gramCovectorOperator_symmetric (B : LinearMap.BilinForm ℝ Z)
    (hB : B.IsSymm) (φ ψ : Module.Dual ℝ Z) :
    φ (gramCovectorOperator B ψ) = ψ (gramCovectorOperator B φ) := by
  rw [gramCovectorOperator_eval, gramCovectorOperator_eval]
  exact hB.eq _ _

theorem gramCovectorOperator_nonneg (B : LinearMap.BilinForm ℝ Z)
    (hB : ∀ X, 0 ≤ B X X) (φ : Module.Dual ℝ Z) :
    0 ≤ φ (gramCovectorOperator B φ) := by
  rw [gramCovectorOperator_eval]
  exact hB _

theorem gramCovectorOperator_zero_iff (B : LinearMap.BilinForm ℝ Z)
    (φ : Module.Dual ℝ Z) :
    gramCovectorOperator B φ = 0 ↔
      ∀ Y : Z, B (coefficientDuality.symm φ) Y = 0 := by
  constructor
  · intro h Y
    have hdual : B (coefficientDuality.symm φ) = 0 := by
      have he := congrArg coefficientDuality h
      simpa [gramCovectorOperator] using he
    exact congrArg (fun f : Module.Dual ℝ Z => f Y) hdual
  · intro h
    have hdual : B (coefficientDuality.symm φ) = 0 := by
      ext Y
      exact h Y
    simp [gramCovectorOperator, hdual]

/-- The ambient 64-pair form represented with the constructed coefficient duality. -/
def ambientDissipation : Module.Dual ℝ Z →ₗ[ℝ] Z :=
  gramCovectorOperator associatorGram

/-- The projected 64-pair form represented with the same constructed duality. -/
def quaternionDissipation : Module.Dual ℝ Z →ₗ[ℝ] Z :=
  gramCovectorOperator projectedAssociatorGram

theorem ambientDissipation_symmetric (φ ψ : Module.Dual ℝ Z) :
    φ (ambientDissipation ψ) = ψ (ambientDissipation φ) :=
  gramCovectorOperator_symmetric associatorGram associatorGram_isSymm φ ψ

theorem ambientDissipation_nonneg (φ : Module.Dual ℝ Z) :
    0 ≤ φ (ambientDissipation φ) :=
  gramCovectorOperator_nonneg associatorGram associatorGram_nonneg φ

theorem quaternionDissipation_symmetric (φ ψ : Module.Dual ℝ Z) :
    φ (quaternionDissipation ψ) = ψ (quaternionDissipation φ) :=
  gramCovectorOperator_symmetric projectedAssociatorGram projectedAssociatorGram_isSymm φ ψ

theorem quaternionDissipation_nonneg (φ : Module.Dual ℝ Z) :
    0 ≤ φ (quaternionDissipation φ) :=
  gramCovectorOperator_nonneg projectedAssociatorGram projectedAssociatorGram_nonneg φ

theorem ambientDissipation_zero_iff (φ : Module.Dual ℝ Z) :
    ambientDissipation φ = 0 ↔
      ∃ r : ℝ, coefficientDuality.symm φ = r • (ZornVectorMatrix.one : Z) :=
  (gramCovectorOperator_zero_iff associatorGram φ).trans
    (associatorGram_left_kernel_iff_scalar _)

theorem quaternionDissipation_zero_iff (φ : Module.Dual ℝ Z) :
    quaternionDissipation φ = 0 ↔
      coefficientDuality.symm φ ∈ LinearMap.range quaternionEmbedding :=
  (gramCovectorOperator_zero_iff projectedAssociatorGram φ).trans
    (projectedAssociatorGram_left_kernel_iff _)

theorem ambientDissipation_quadratic_zero_iff (φ : Module.Dual ℝ Z) :
    φ (ambientDissipation φ) = 0 ↔
      ∃ r : ℝ, coefficientDuality.symm φ = r • (ZornVectorMatrix.one : Z) := by
  change φ (gramCovectorOperator associatorGram φ) = 0 ↔ _
  rw [gramCovectorOperator_eval]
  exact associatorGram_zero_iff_scalar _

theorem quaternionDissipation_quadratic_zero_iff (φ : Module.Dual ℝ Z) :
    φ (quaternionDissipation φ) = 0 ↔
      coefficientDuality.symm φ ∈ LinearMap.range quaternionEmbedding := by
  change φ (gramCovectorOperator projectedAssociatorGram φ) = 0 ↔ _
  rw [gramCovectorOperator_eval]
  exact projectedAssociatorGram_zero_iff _

/-- A concrete covector has strictly positive dissipation, so the constructed
positive operator is not the zero map. -/
theorem quaternionDissipation_E11_pos :
    0 < coefficientDuality (ZornVectorMatrix.E11 : Z)
      (quaternionDissipation (coefficientDuality ZornVectorMatrix.E11)) := by
  change 0 < coefficientDuality (ZornVectorMatrix.E11 : Z)
    (gramCovectorOperator projectedAssociatorGram (coefficientDuality ZornVectorMatrix.E11))
  simp only [gramCovectorOperator_eval, LinearEquiv.symm_apply_apply]
  exact projectedAssociatorGram_E11_pos

end InfoGeometry.Algebra.ZornGramDissipation

end
