/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedTensorMorita
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Transpose-compatible adjoint on a native graded Clifford tensor product

The Clifford head adjoint is transported from real matrix transpose through
the existing faithful standard representation. This is deliberately not the
canonical Clifford-conjugation instance in Mathlib: the positive generator
is fixed and the negative generator changes sign.

The tensor adjoint uses conjugate transpose over the entire coefficient star
algebra. It is an ordinary product-reversing anti-involution. Its homogeneous
formula contains the Koszul sign, assuming coefficient parity commutes with
star. Coefficients need not commute or be finite dimensional. No positivity,
norm, completion, or global replacement star instance is asserted.
-/

noncomputable section

open scoped Matrix Matrix.Module TensorProduct

namespace InfoGeometry.Clifford.Cl11GradedAdjoint

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita

/-- The transpose convention on the actual native split Clifford algebra. -/
def headAdjoint (x : CliffordAlgebra q11) : CliffordAlgebra q11 :=
  cl11StandardEquiv.symm (cl11StandardEquiv x)ᵀ

@[simp] theorem represent_headAdjoint (x : CliffordAlgebra q11) :
    cl11StandardEquiv (headAdjoint x) = (cl11StandardEquiv x)ᵀ :=
  cl11StandardEquiv.apply_symm_apply _

@[simp] theorem headAdjoint_headAdjoint (x : CliffordAlgebra q11) :
    headAdjoint (headAdjoint x) = x := by
  apply cl11StandardEquiv.injective
  simp

theorem headAdjoint_mul (x y : CliffordAlgebra q11) :
    headAdjoint (x * y) = headAdjoint y * headAdjoint x := by
  apply cl11StandardEquiv.injective
  simp [Matrix.transpose_mul]

@[simp] theorem headAdjoint_add (x y : CliffordAlgebra q11) :
    headAdjoint (x + y) = headAdjoint x + headAdjoint y := by
  apply cl11StandardEquiv.injective
  simp

@[simp] theorem headAdjoint_smul (r : ℝ) (x : CliffordAlgebra q11) :
    headAdjoint (r • x) = r • headAdjoint x := by
  apply cl11StandardEquiv.injective
  simp

@[simp] theorem headAdjoint_one : headAdjoint 1 = 1 := by
  apply cl11StandardEquiv.injective
  simp

/-- The positive Clifford generator is self-adjoint in this convention. -/
@[simp] theorem headAdjoint_positive :
    headAdjoint (CliffordAlgebra.ι q11 (1, 0)) =
      CliffordAlgebra.ι q11 (1, 0) := by
  apply cl11StandardEquiv.injective
  simp [J1_transpose]

/-- The negative Clifford generator is skew-adjoint in this convention. -/
@[simp] theorem headAdjoint_negative :
    headAdjoint (CliffordAlgebra.ι q11 (0, 1)) =
      -CliffordAlgebra.ι q11 (0, 1) := by
  apply cl11StandardEquiv.injective
  simp only [represent_headAdjoint, cl11StandardEquiv_iota_neg, map_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Eminus, Matrix.transpose_apply]

/-- The chosen adjoint retains a concrete noncommuting native Clifford pair. -/
theorem headAdjoint_generators_noncommuting :
    ¬Commute (headAdjoint (CliffordAlgebra.ι q11 (1, 0)))
      (headAdjoint (CliffordAlgebra.ι q11 (0, 1))) := by
  intro h
  apply J1_mul_Eminus_ne
  have hm := congrArg cl11StandardEquiv h.eq
  simpa only [map_mul, headAdjoint_positive, headAdjoint_negative, map_neg,
    cl11StandardEquiv_iota_pos, cl11StandardEquiv_iota_neg, neg_neg] using hm

/-- The even Clifford grading implementer is self-adjoint. -/
@[simp] theorem headAdjoint_volume : headAdjoint J1_cl = J1_cl := by
  apply cl11StandardEquiv.injective
  simp only [represent_headAdjoint, cl11StandardEquiv_J1_cl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Eplus]

/-- The chosen head adjoint preserves the canonical Clifford parity. -/
theorem headAdjoint_involute (x : CliffordAlgebra q11) :
    headAdjoint (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (headAdjoint x) := by
  apply cl11StandardEquiv.injective
  rw [represent_headAdjoint, cl11StandardEquiv_involute,
    cl11StandardEquiv_involute, represent_headAdjoint]
  have hE : Eplusᵀ = Eplus := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Eplus]
  simp [Matrix.transpose_mul, hE, mul_assoc]

universe u

variable {A : Type u} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]
variable (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
variable (θ : A ≃ₐ[ℝ] A)
variable (hEven : ∀ {a : A}, a ∈ 𝒜 0 → θ a = a)
variable (hOdd : ∀ {a : A}, a ∈ 𝒜 1 → θ a = -a)

/-- Pull back matrix conjugate transpose through the actual graded lift. -/
def tensorAdjoint (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜 :=
  (tensorMatrixEquiv 𝒜 θ hEven hOdd).symm
    (tensorMatrixEquiv 𝒜 θ hEven hOdd z)ᴴ

@[simp] theorem represent_tensorAdjoint
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd (tensorAdjoint 𝒜 θ hEven hOdd z) =
      (tensorMatrixEquiv 𝒜 θ hEven hOdd z)ᴴ :=
  (tensorMatrixEquiv 𝒜 θ hEven hOdd).apply_symm_apply _

@[simp] theorem tensorAdjoint_tensorAdjoint
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorAdjoint 𝒜 θ hEven hOdd (tensorAdjoint 𝒜 θ hEven hOdd z) = z := by
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  simp only [represent_tensorAdjoint, Matrix.conjTranspose_conjTranspose]

/-- Multiplication reverses in the full noncommutative coefficient algebra. -/
theorem tensorAdjoint_mul (x y : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorAdjoint 𝒜 θ hEven hOdd (x * y) =
      tensorAdjoint 𝒜 θ hEven hOdd y * tensorAdjoint 𝒜 θ hEven hOdd x := by
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  simp only [represent_tensorAdjoint, map_mul, Matrix.conjTranspose_mul]

@[simp] theorem tensorAdjoint_add (x y : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorAdjoint 𝒜 θ hEven hOdd (x + y) =
      tensorAdjoint 𝒜 θ hEven hOdd x + tensorAdjoint 𝒜 θ hEven hOdd y := by
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  simp only [represent_tensorAdjoint, map_add, Matrix.conjTranspose_add]

@[simp] theorem tensorAdjoint_smul (r : ℝ)
    (x : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorAdjoint 𝒜 θ hEven hOdd (r • x) =
      r • tensorAdjoint 𝒜 θ hEven hOdd x := by
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  simp only [represent_tensorAdjoint, map_smul, Matrix.conjTranspose_smul, star_trivial]

@[simp] theorem tensorAdjoint_one : tensorAdjoint 𝒜 θ hEven hOdd 1 = 1 := by
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  simp only [represent_tensorAdjoint, map_one, Matrix.conjTranspose_one]

/-- An actual involutive real linear equivalence, with no replacement carrier. -/
def tensorAdjointLinear :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) ≃ₗ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) where
  toFun := tensorAdjoint 𝒜 θ hEven hOdd
  invFun := tensorAdjoint 𝒜 θ hEven hOdd
  left_inv := tensorAdjoint_tensorAdjoint 𝒜 θ hEven hOdd
  right_inv := tensorAdjoint_tensorAdjoint 𝒜 θ hEven hOdd
  map_add' := tensorAdjoint_add 𝒜 θ hEven hOdd
  map_smul' := tensorAdjoint_smul 𝒜 θ hEven hOdd

/-- Idempotence survives the transported adjoint; no parity hypothesis is
needed for this consequence of the proved anti-involution. -/
theorem tensorAdjoint_idempotent
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) (hz : z * z = z) :
    tensorAdjoint 𝒜 θ hEven hOdd z * tensorAdjoint 𝒜 θ hEven hOdd z =
      tensorAdjoint 𝒜 θ hEven hOdd z := by
  rw [← tensorAdjoint_mul, hz]

variable (hStar : ∀ a : A, θ (star a) = star (θ a))

include hStar

/-- Product parity commutes with the adjoint on every tensor, not only on
homogeneous simple tensors. -/
theorem tensorAdjoint_parity
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorAdjoint 𝒜 θ hEven hOdd (tensorParity 𝒜 θ hEven hOdd z) =
      tensorParity 𝒜 θ hEven hOdd (tensorAdjoint 𝒜 θ hEven hOdd z) := by
  have hp (w : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
      tensorMatrixEquiv 𝒜 θ hEven hOdd (tensorParity 𝒜 θ hEven hOdd w) =
        matrixGrade θ.toRingEquiv (tensorMatrixEquiv 𝒜 θ hEven hOdd w) :=
    tensorParity_compatible 𝒜 θ hEven hOdd w
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  rw [represent_tensorAdjoint, hp, hp, represent_tensorAdjoint]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade_apply,
      Matrix.conjTranspose_apply, hStar]

/-- The Koszul sign is proved on native homogeneous components. The only
star/parity hypothesis concerns the actual coefficient algebra. -/
theorem tensorAdjoint_tmul_homogeneous {i j : ZMod 2}
    (x : CliffordAlgebra.evenOdd q11 i) (a : 𝒜 j) :
    tensorAdjoint 𝒜 θ hEven hOdd ((x : CliffordAlgebra q11) ᵍ⊗ₜ (a : A)) =
      (-1 : ℤˣ) ^ (i * j) • (headAdjoint (x : CliffordAlgebra q11) ᵍ⊗ₜ star (a : A)) := by
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  rw [represent_tensorAdjoint]
  fin_cases i <;> fin_cases j
  · change (tensorMatrixEquiv 𝒜 θ hEven hOdd
        ((x : CliffordAlgebra q11) ᵍ⊗ₜ (a : A)))ᴴ =
      tensorMatrixEquiv 𝒜 θ hEven hOdd
        ((-1 : ℤˣ) ^ (0 : ZMod 2) •
          (headAdjoint (x : CliffordAlgebra q11) ᵍ⊗ₜ star (a : A)))
    rw [uzpow_zero, one_smul]
    rw [tensorMatrixEquiv_apply, tensorMatrixEquiv_apply,
      tensorToMatrix_tmul_matrix, tensorToMatrix_tmul_matrix, represent_headAdjoint]
    have ha := hEven a.property
    ext r s
    fin_cases r <;> fin_cases s <;> simp [ha, hStar, Matrix.conjTranspose_apply]
  · change (tensorMatrixEquiv 𝒜 θ hEven hOdd
        ((x : CliffordAlgebra q11) ᵍ⊗ₜ (a : A)))ᴴ =
      tensorMatrixEquiv 𝒜 θ hEven hOdd
        ((-1 : ℤˣ) ^ (0 : ZMod 2) •
          (headAdjoint (x : CliffordAlgebra q11) ᵍ⊗ₜ star (a : A)))
    rw [uzpow_zero, one_smul]
    rw [tensorMatrixEquiv_apply, tensorMatrixEquiv_apply,
      tensorToMatrix_tmul_matrix, tensorToMatrix_tmul_matrix, represent_headAdjoint]
    have ha := hOdd a.property
    obtain ⟨hx01, hx10⟩ := cl11StandardEquiv_even_offDiagonal x.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [ha, hStar, hx01, hx10, Matrix.conjTranspose_apply]
  · change (tensorMatrixEquiv 𝒜 θ hEven hOdd
        ((x : CliffordAlgebra q11) ᵍ⊗ₜ (a : A)))ᴴ =
      tensorMatrixEquiv 𝒜 θ hEven hOdd
        ((-1 : ℤˣ) ^ (0 : ZMod 2) •
          (headAdjoint (x : CliffordAlgebra q11) ᵍ⊗ₜ star (a : A)))
    rw [uzpow_zero, one_smul]
    rw [tensorMatrixEquiv_apply, tensorMatrixEquiv_apply,
      tensorToMatrix_tmul_matrix, tensorToMatrix_tmul_matrix, represent_headAdjoint]
    have ha := hEven a.property
    ext r s
    fin_cases r <;> fin_cases s <;> simp [ha, hStar, Matrix.conjTranspose_apply]
  · change (tensorMatrixEquiv 𝒜 θ hEven hOdd
        ((x : CliffordAlgebra q11) ᵍ⊗ₜ (a : A)))ᴴ =
      tensorMatrixEquiv 𝒜 θ hEven hOdd
        ((-1 : ℤˣ) ^ (1 : ZMod 2) •
          (headAdjoint (x : CliffordAlgebra q11) ᵍ⊗ₜ star (a : A)))
    rw [uzpow_one, Units.neg_smul, one_smul, map_neg]
    rw [tensorMatrixEquiv_apply, tensorMatrixEquiv_apply,
      tensorToMatrix_tmul_matrix, tensorToMatrix_tmul_matrix, represent_headAdjoint]
    have ha := hOdd a.property
    obtain ⟨hx00, hx11⟩ := cl11StandardEquiv_odd_diagonal x.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [ha, hStar, hx00, hx11, Matrix.conjTranspose_apply]

end InfoGeometry.Clifford.Cl11GradedAdjoint
