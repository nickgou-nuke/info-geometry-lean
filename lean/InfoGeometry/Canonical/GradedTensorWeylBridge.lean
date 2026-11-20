/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11GradedTensorMorita
import Mathlib.Tactic

/-!
# Native graded tensor product of two real `2 × 2` matrix algebras

This owner uses Mathlib's `GradedTensorProduct` carrier, not an ordinary
Kronecker tensor with a parity formula appended afterward. Each factor is
`M₂(ℝ)` with the checkerboard grading induced by conjugation with
`diag(1,-1)`: diagonal matrix units are even and off-diagonal units are odd.
The native multiplication therefore inserts the Koszul sign.

The proved scope here is the graded algebra and the complete two-mode CAR
table for its canonical upper/lower matrix-unit generators, including the
same-factor mixed relation and all cross-factor anticommutators. An algebra
equivalence from this particular
`M₂(ℝ) ᵍ⊗ M₂(ℝ)` carrier to `M₄(ℝ)` is not asserted by the ordinary
Kronecker identity; it requires a graded/Jordan–Wigner representation map.
The separate `Cl(1,1) ᵍ⊗ M₂(ℝ) ≃ M₂(M₂(ℝ))` construction is owned by
`Cl11GradedTensorMorita`.
-/

noncomputable section

namespace InfoGeometry.Canonical.GradedTensorWeylBridge

open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita
open scoped TensorProduct GradedTensorProduct

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The parity automorphism on `M₂(ℝ)`, conjugation by `diag(1,-1)`. -/
def matrixParity : M2R ≃ₐ[ℝ] M2R :=
  matrixAlgGrade (A := ℝ) (AlgEquiv.refl : ℝ ≃ₐ[ℝ] ℝ)

theorem matrixParity_involutive : Function.Involutive matrixParity := by
  exact matrixAlgGrade_involutive (A := ℝ)
    (AlgEquiv.refl : ℝ ≃ₐ[ℝ] ℝ) (by intro x; rfl)

@[simp] theorem matrixParity_apply (A : M2R) :
    matrixParity A = !![A 0 0, -A 0 1; -A 1 0, A 1 1] := rfl

/-- Native `ZMod 2` decomposition of the real matrix algebra. -/
abbrev matrixGrading : ZMod 2 → Submodule ℝ M2R :=
  involutionGrading matrixParity matrixParity_involutive

instance matrixGradingAlgebra : GradedAlgebra matrixGrading :=
  instGradedAlgebraInvolutionGrading matrixParity matrixParity_involutive

/-- The actual super tensor product of the two graded real matrix algebras. -/
abbrev twoMatrixGradedTensor := matrixGrading ᵍ⊗[ℝ] matrixGrading

/-- First off-diagonal matrix unit; it is odd for checkerboard parity. -/
def matrixE01 : M2R := Matrix.single 0 1 1

/-- Opposite off-diagonal matrix unit, used as the creation operator. -/
def matrixE10 : M2R := Matrix.single 1 0 1

theorem matrixE01_odd : matrixE01 ∈ matrixGrading 1 := by
  change matrixParity matrixE01 = -matrixE01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixE01, matrixParity_apply, Matrix.single]

theorem matrixE10_odd : matrixE10 ∈ matrixGrading 1 := by
  change matrixParity matrixE10 = -matrixE10
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixE10, matrixParity_apply, Matrix.single]

/-- The unit matrix is even. -/
theorem matrixOne_even : (1 : M2R) ∈ matrixGrading 0 := by
  change matrixParity (1 : M2R) = 1
  exact map_one matrixParity

/-- Product of the two odd generators in the forward tensor order. -/
theorem oddFactorGenerators_mul_forward :
    ((matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) : twoMatrixGradedTensor) *
      (((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) : twoMatrixGradedTensor) =
      (matrixE01 ᵍ⊗ₜ[ℝ] matrixE01 : twoMatrixGradedTensor) := by
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
    (matrixE01) (⟨1, matrixOne_even⟩ : matrixGrading 0)
    (⟨1, matrixOne_even⟩ : matrixGrading 0) (matrixE01)]
  simp

/-- Reversing the two odd generators contributes exactly the Koszul minus. -/
theorem oddFactorGenerators_mul_reverse :
    (((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) : twoMatrixGradedTensor) *
      ((matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) : twoMatrixGradedTensor) =
      -(matrixE01 ᵍ⊗ₜ[ℝ] matrixE01 : twoMatrixGradedTensor) := by
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
    (1 : M2R) (⟨matrixE01, matrixE01_odd⟩ : matrixGrading 1)
    (⟨matrixE01, matrixE01_odd⟩ : matrixGrading 1) (1 : M2R)]
  simp

/-- The odd factor generators anticommute in the native graded tensor
algebra. -/
theorem gradedTensor_odd_anticommute :
    ((matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) : twoMatrixGradedTensor) *
        ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01 : twoMatrixGradedTensor) +
      ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01 : twoMatrixGradedTensor) *
        ((matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) : twoMatrixGradedTensor) = 0 := by
  rw [oddFactorGenerators_mul_forward, oddFactorGenerators_mul_reverse]
  exact add_neg_cancel _

/-- The first real fermionic annihilation mode. -/
def annihilation₀ : twoMatrixGradedTensor :=
  matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)

/-- The second real fermionic annihilation mode. -/
def annihilation₁ : twoMatrixGradedTensor :=
  (1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01

/-- Creation operators are the opposite matrix units in each factor. -/
def creation₀ : twoMatrixGradedTensor :=
  matrixE10 ᵍ⊗ₜ[ℝ] (1 : M2R)

def creation₁ : twoMatrixGradedTensor :=
  (1 : M2R) ᵍ⊗ₜ[ℝ] matrixE10

private theorem matrixE01_mul_self : matrixE01 * matrixE01 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixE01, Matrix.single,
    Matrix.mul_apply]

private theorem matrixE10_mul_self : matrixE10 * matrixE10 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixE10, Matrix.single,
    Matrix.mul_apply]

private theorem matrixCAR :
    matrixE01 * matrixE10 + matrixE10 * matrixE01 = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixE01, matrixE10, Matrix.single, Matrix.mul_apply]

private theorem gradedTmul_add_left {A B : Type*} [Ring A] [Ring B]
    [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (a₁ a₂ : A) (b : B) :
    ((a₁ + a₂) ᵍ⊗ₜ[ℝ] b : 𝒜 ᵍ⊗[ℝ] ℬ) = a₁ ᵍ⊗ₜ b + a₂ ᵍ⊗ₜ b := by
  dsimp [GradedTensorProduct.tmul]
  rw [TensorProduct.add_tmul, map_add]

private theorem gradedTmul_add_right {A B : Type*} [Ring A] [Ring B]
    [Algebra ℝ A] [Algebra ℝ B]
    {𝒜 : ZMod 2 → Submodule ℝ A} {ℬ : ZMod 2 → Submodule ℝ B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (a : A) (b₁ b₂ : B) :
    (a ᵍ⊗ₜ[ℝ] (b₁ + b₂) : 𝒜 ᵍ⊗[ℝ] ℬ) = a ᵍ⊗ₜ b₁ + a ᵍ⊗ₜ b₂ := by
  dsimp [GradedTensorProduct.tmul]
  rw [TensorProduct.tmul_add, map_add]

/-- The two opposite matrix units give the local CAR in the first graded
factor, with the second factor equal to its unit. -/
theorem annihilation₀_creation₀_CAR :
    annihilation₀ * creation₀ + creation₀ * annihilation₀ = 1 := by
  have h01 := matrixE01_odd
  have h10 := matrixE10_odd
  have h1 := matrixOne_even
  change (matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) *
      (matrixE10 ᵍ⊗ₜ[ℝ] (1 : M2R)) +
    (matrixE10 ᵍ⊗ₜ[ℝ] (1 : M2R)) *
      (matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) = 1
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      matrixE01 (⟨(1 : M2R), h1⟩ : matrixGrading 0)
      (⟨matrixE10, h10⟩ : matrixGrading 1) (1 : M2R),
    GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      matrixE10 (⟨(1 : M2R), h1⟩ : matrixGrading 0)
      (⟨matrixE01, h01⟩ : matrixGrading 1) (1 : M2R)]
  norm_num
  rw [← gradedTmul_add_left (matrixE01 * matrixE10)
    (matrixE10 * matrixE01) (1 : M2R)]
  rw [matrixCAR]
  rfl

/-- The two opposite matrix units give the local CAR in the second graded
factor, with the first factor equal to its unit. -/
theorem annihilation₁_creation₁_CAR :
    annihilation₁ * creation₁ + creation₁ * annihilation₁ = 1 := by
  have h01 := matrixE01_odd
  have h10 := matrixE10_odd
  have h1 := matrixOne_even
  change ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) *
      ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE10) +
    ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE10) *
      ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) = 1
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      (1 : M2R) (⟨matrixE01, h01⟩ : matrixGrading 1)
      (⟨(1 : M2R), h1⟩ : matrixGrading 0) matrixE10,
    GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      (1 : M2R) (⟨matrixE10, h10⟩ : matrixGrading 1)
      (⟨(1 : M2R), h1⟩ : matrixGrading 0) matrixE01]
  norm_num
  rw [← gradedTmul_add_right (1 : M2R)
    (matrixE01 * matrixE10) (matrixE10 * matrixE01)]
  rw [matrixCAR]
  rfl

/-- Each embedded annihilation operator is nilpotent. -/
theorem annihilation₀_sq : annihilation₀ * annihilation₀ = 0 := by
  change (matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) *
    (matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) = 0
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
    matrixE01 (⟨(1 : M2R), matrixOne_even⟩ : matrixGrading 0)
    (⟨matrixE01, matrixE01_odd⟩ : matrixGrading 1) (1 : M2R)]
  simp [matrixE01_mul_self]

theorem annihilation₁_sq : annihilation₁ * annihilation₁ = 0 := by
  change ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) *
    ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) = 0
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
    (1 : M2R) (⟨matrixE01, matrixE01_odd⟩ : matrixGrading 1)
    (⟨(1 : M2R), matrixOne_even⟩ : matrixGrading 0) matrixE01]
  simp [matrixE01_mul_self]

/-- Different real tensor factors anticommute for odd matrix units; this is
the two-mode CAR sign in the actual graded tensor product. -/
theorem annihilation₀_annihilation₁_anticommute :
    annihilation₀ * annihilation₁ + annihilation₁ * annihilation₀ = 0 := by
  change (matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) *
      ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) +
    ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) *
      (matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) = 0
  rw [oddFactorGenerators_mul_forward, oddFactorGenerators_mul_reverse]
  exact add_neg_cancel _

/-- The mixed annihilation/creation cross relation also carries the Koszul
minus sign, so its anticommutator vanishes. -/
theorem annihilation₀_creation₁_anticommute :
    annihilation₀ * creation₁ + creation₁ * annihilation₀ = 0 := by
  have h01 : matrixE01 ∈ matrixGrading 1 := matrixE01_odd
  have h10 : matrixE10 ∈ matrixGrading 1 := matrixE10_odd
  have h1 : (1 : M2R) ∈ matrixGrading 0 := matrixOne_even
  change (matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) *
      ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE10) +
    ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE10) *
      (matrixE01 ᵍ⊗ₜ[ℝ] (1 : M2R)) = 0
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      matrixE01 (⟨(1 : M2R), h1⟩ : matrixGrading 0)
      (⟨(1 : M2R), h1⟩ : matrixGrading 0) matrixE10,
    GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      (1 : M2R) (⟨matrixE10, h10⟩ : matrixGrading 1)
      (⟨matrixE01, h01⟩ : matrixGrading 1) (1 : M2R)]
  simp

/-- The other mixed cross-mode CAR relation in the native real supertensor. -/
theorem annihilation₁_creation₀_anticommute :
    annihilation₁ * creation₀ + creation₀ * annihilation₁ = 0 := by
  have h01 : matrixE01 ∈ matrixGrading 1 := matrixE01_odd
  have h10 : matrixE10 ∈ matrixGrading 1 := matrixE10_odd
  have h1 : (1 : M2R) ∈ matrixGrading 0 := matrixOne_even
  change ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) *
      (matrixE10 ᵍ⊗ₜ[ℝ] (1 : M2R)) +
    (matrixE10 ᵍ⊗ₜ[ℝ] (1 : M2R)) *
      ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE01) = 0
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      (1 : M2R) (⟨matrixE01, h01⟩ : matrixGrading 1)
      (⟨matrixE10, h10⟩ : matrixGrading 1) (1 : M2R),
    GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      matrixE10 (⟨(1 : M2R), h1⟩ : matrixGrading 0)
      (⟨(1 : M2R), h1⟩ : matrixGrading 0) matrixE01]
  simp

/-- Distinct creation factors anticommute by the Koszul sign. -/
theorem creation₀_creation₁_anticommute :
    creation₀ * creation₁ + creation₁ * creation₀ = 0 := by
  have h10 : matrixE10 ∈ matrixGrading 1 := matrixE10_odd
  have h1 : (1 : M2R) ∈ matrixGrading 0 := matrixOne_even
  change (matrixE10 ᵍ⊗ₜ[ℝ] (1 : M2R)) *
      ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE10) +
    ((1 : M2R) ᵍ⊗ₜ[ℝ] matrixE10) *
      (matrixE10 ᵍ⊗ₜ[ℝ] (1 : M2R)) = 0
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      matrixE10 (⟨(1 : M2R), h1⟩ : matrixGrading 0)
      (⟨(1 : M2R), h1⟩ : matrixGrading 0) matrixE10,
    GradedTensorProduct.tmul_coe_mul_coe_tmul matrixGrading matrixGrading
      (1 : M2R) (⟨matrixE10, h10⟩ : matrixGrading 1)
      (⟨matrixE10, h10⟩ : matrixGrading 1) (1 : M2R)]
  simp

end InfoGeometry.Canonical.GradedTensorWeylBridge
