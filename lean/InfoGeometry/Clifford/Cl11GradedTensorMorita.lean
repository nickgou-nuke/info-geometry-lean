/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedMorita
import InfoGeometry.OperatorAlgebra.GradedMatrixMorita
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

/-!
# Cancellation of a split Clifford head with graded coefficients

For an arbitrary real algebra `A` with a native `ZMod 2` grading, the graded
tensor product `Cl(1,1) ᵍ⊗ A` is represented on two-by-two matrices over the
full coefficient algebra. The tail action is `diag(a, θ a)`, where `θ`
is the coefficient grading automorphism. Its signs supply the actual Koszul
commutation relation required by the native graded tensor universal property.

An explicit inverse expands a matrix in four native matrix units. Thus no
finite-dimensionality or commutativity of the coefficient algebra is used.
The product parity is constructed as `involute ⊗ θ`; its compatibility with
matrix parity is proved on every tensor. The resulting graded module category
equivalence cancels the head while retaining all of the residual action.
-/

noncomputable section

open CategoryTheory
open scoped Matrix Matrix.Module TensorProduct

namespace InfoGeometry.Clifford.Cl11GradedTensorMorita

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita

universe u

variable {A : Type u} [Ring A] [Algebra ℝ A]

/-- The standard Clifford head with scalar coefficients extended into `A`. -/
def head : CliffordAlgebra q11 →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  (Algebra.ofId ℝ A).mapMatrix.comp cl11StandardEquiv.toAlgHom

@[simp] theorem head_apply (x : CliffordAlgebra q11) (i j : Fin 2) :
    head (A := A) x i j = algebraMap ℝ A (cl11StandardEquiv x i j) := rfl

/-- The coefficient action with the parity twist on the second coordinate. -/
def tail (θ : A ≃ₐ[ℝ] A) : A →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A where
  toFun a := !![a, 0; 0, θ a]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem tail_apply (θ : A ≃ₐ[ℝ] A) (a : A) :
    tail θ a = !![a, 0; 0, θ a] := rfl

private theorem scalar_comm (r : ℝ) (a : A) :
    algebraMap ℝ A r * a = a * algebraMap ℝ A r :=
  (Algebra.commutes r a).eq

variable (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
variable (θ : A ≃ₐ[ℝ] A)
variable (hEven : ∀ {a : A}, a ∈ 𝒜 0 → θ a = a)
variable (hOdd : ∀ {a : A}, a ∈ 𝒜 1 → θ a = -a)

/-- The sign action on the native homogeneous components forces the
coefficient automorphism to be involutive on the entire algebra. -/
theorem coefficientParity_involutive : Function.Involutive θ := by
  have h : θ.toLinearMap.comp θ.toLinearMap = LinearMap.id := by
    apply DirectSum.decompose_lhom_ext 𝒜
    intro i
    apply LinearMap.ext
    intro a
    change θ (θ (a : A)) = (a : A)
    fin_cases i
    · rw [hEven a.property, hEven a.property]
    · rw [hOdd a.property, map_neg, hOdd a.property, neg_neg]
  intro a
  exact LinearMap.congr_fun h a

/-- The exact supercommutation relation needed by the native graded tensor
product. Only real head coefficients commute with the residual algebra. -/
theorem head_tail_supercommute {i j : ZMod 2}
    (x : CliffordAlgebra.evenOdd q11 i) (a : 𝒜 j) :
    head (A := A) x * tail θ a =
      (-1 : ℤˣ) ^ (j * i) • (tail θ a * head (A := A) x) := by
  fin_cases i <;> fin_cases j
  · have ha := hEven a.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ← scalar_comm]
  · have ha := hOdd a.property
    obtain ⟨hx01, hx10⟩ := cl11StandardEquiv_even_offDiagonal x.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hx01, hx10, ← scalar_comm]
  · have ha := hEven a.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ← scalar_comm]
  · have ha := hOdd a.property
    obtain ⟨hx00, hx11⟩ := cl11StandardEquiv_odd_diagonal x.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hx00, hx11,
        Units.smul_def, ← scalar_comm]

/-- The representation is constructed by the native graded tensor lift. -/
def tensorToMatrix :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  GradedTensorProduct.lift (CliffordAlgebra.evenOdd q11) 𝒜
    (head (A := A)) (tail θ) (head_tail_supercommute 𝒜 θ hEven hOdd)

@[simp] theorem tensorToMatrix_tmul (x : CliffordAlgebra q11) (a : A) :
    tensorToMatrix 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a) = head x * tail θ a := rfl

/-- The explicit entry formula retains multiplication by every coefficient. -/
theorem tensorToMatrix_tmul_matrix (x : CliffordAlgebra q11) (a : A) :
    tensorToMatrix 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a) =
      !![cl11StandardEquiv x 0 0 • a, cl11StandardEquiv x 0 1 • θ a;
         cl11StandardEquiv x 1 0 • a, cl11StandardEquiv x 1 1 • θ a] := by
  rw [tensorToMatrix_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]

/-- Native Clifford preimages of the four elementary matrices. -/
def headUnit (i j : Fin 2) : CliffordAlgebra q11 :=
  cl11StandardEquiv.symm (Matrix.single i j 1)

@[simp] theorem cl11StandardEquiv_headUnit (i j : Fin 2) :
    cl11StandardEquiv (headUnit i j) = Matrix.single i j 1 :=
  cl11StandardEquiv.apply_symm_apply _

private theorem headUnit_expansion (x : CliffordAlgebra q11) :
    cl11StandardEquiv x 0 0 • headUnit 0 0 +
        cl11StandardEquiv x 0 1 • headUnit 0 1 +
        cl11StandardEquiv x 1 0 • headUnit 1 0 +
        cl11StandardEquiv x 1 1 • headUnit 1 1 = x := by
  apply cl11StandardEquiv.injective
  simp only [map_add, map_smul, cl11StandardEquiv_headUnit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

private def unitTensor (i j : Fin 2) :
    A →ₗ[ℝ] (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :=
  (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).toLinearMap.comp
    (TensorProduct.mk ℝ (CliffordAlgebra q11) A (headUnit i j))

/-- The inverse expansion twists the second matrix column back by `θ⁻¹`. -/
def matrixToTensor :
    Matrix (Fin 2) (Fin 2) A →ₗ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :=
  (unitTensor 𝒜 0 0).comp (Matrix.entryLinearMap ℝ A 0 0) +
    (unitTensor 𝒜 0 1).comp
      (θ.symm.toLinearMap.comp (Matrix.entryLinearMap ℝ A 0 1)) +
    (unitTensor 𝒜 1 0).comp (Matrix.entryLinearMap ℝ A 1 0) +
    (unitTensor 𝒜 1 1).comp
      (θ.symm.toLinearMap.comp (Matrix.entryLinearMap ℝ A 1 1))

theorem matrixToTensor_apply (M : Matrix (Fin 2) (Fin 2) A) :
    matrixToTensor 𝒜 θ M =
      (headUnit 0 0 ᵍ⊗ₜ M 0 0) +
        (headUnit 0 1 ᵍ⊗ₜ θ.symm (M 0 1)) +
        (headUnit 1 0 ᵍ⊗ₜ M 1 0) +
        (headUnit 1 1 ᵍ⊗ₜ θ.symm (M 1 1)) := rfl

private theorem matrixToTensor_tmul (x : CliffordAlgebra q11) (a : A) :
    matrixToTensor 𝒜 θ (tensorToMatrix 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a)) =
      (x ᵍ⊗ₜ a) := by
  rw [tensorToMatrix_tmul_matrix, matrixToTensor_apply]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_smul,
    AlgEquiv.symm_apply_apply]
  apply (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).symm.injective
  change
    headUnit 0 0 ⊗ₜ[ℝ] (cl11StandardEquiv x 0 0 • a) +
        headUnit 0 1 ⊗ₜ[ℝ] (cl11StandardEquiv x 0 1 • a) +
        headUnit 1 0 ⊗ₜ[ℝ] (cl11StandardEquiv x 1 0 • a) +
        headUnit 1 1 ⊗ₜ[ℝ] (cl11StandardEquiv x 1 1 • a) = x ⊗ₜ[ℝ] a
  rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← TensorProduct.add_tmul, ← TensorProduct.add_tmul,
    ← TensorProduct.add_tmul, headUnit_expansion]

/-- The inverse reconstructs every tensor, by its native tensor induction. -/
theorem matrixToTensor_tensorToMatrix
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    matrixToTensor 𝒜 θ (tensorToMatrix 𝒜 θ hEven hOdd z) = z := by
  obtain ⟨t, rfl⟩ :=
    (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul x a => exact matrixToTensor_tmul 𝒜 θ hEven hOdd x a
  | add x y hx hy => simpa only [map_add, hx, hy]

/-- Every matrix is reached; the coefficient algebra may be infinite-dimensional. -/
theorem tensorToMatrix_matrixToTensor (M : Matrix (Fin 2) (Fin 2) A) :
    tensorToMatrix 𝒜 θ hEven hOdd (matrixToTensor 𝒜 θ M) = M := by
  rw [matrixToTensor_apply]
  simp only [map_add, tensorToMatrix_tmul_matrix, cl11StandardEquiv_headUnit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

/-- The actual graded tensor presentation of a split Clifford head over
arbitrary residual coefficients. Its bijectivity comes from the inverse above. -/
def tensorMatrixEquiv :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  AlgEquiv.ofBijective (tensorToMatrix 𝒜 θ hEven hOdd)
    ⟨Function.LeftInverse.injective (matrixToTensor_tensorToMatrix 𝒜 θ hEven hOdd),
      Function.RightInverse.surjective (tensorToMatrix_matrixToTensor 𝒜 θ hEven hOdd)⟩

@[simp] theorem tensorMatrixEquiv_apply
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd z = tensorToMatrix 𝒜 θ hEven hOdd z := rfl

theorem tensorMatrixEquiv_symm_apply (M : Matrix (Fin 2) (Fin 2) A) :
    (tensorMatrixEquiv 𝒜 θ hEven hOdd).symm M = matrixToTensor 𝒜 θ M := by
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  rw [AlgEquiv.apply_symm_apply, tensorMatrixEquiv_apply,
    tensorToMatrix_matrixToTensor]

/-- The faithful tensor presentation retains explicit noncommuting matrix
units; cancellation has not replaced the algebra by commuting coefficients. -/
theorem tensor_matrix_units_noncomm [Nontrivial A] :
    (tensorMatrixEquiv 𝒜 θ hEven hOdd).symm (Matrix.single (0 : Fin 2) 1 (1 : A)) *
        (tensorMatrixEquiv 𝒜 θ hEven hOdd).symm (Matrix.single 1 0 1) ≠
      (tensorMatrixEquiv 𝒜 θ hEven hOdd).symm (Matrix.single (1 : Fin 2) 0 (1 : A)) *
        (tensorMatrixEquiv 𝒜 θ hEven hOdd).symm (Matrix.single 0 1 1) := by
  intro h
  apply matrix_units_noncomm (A := A)
  have hm := congrArg (tensorMatrixEquiv 𝒜 θ hEven hOdd) h
  simpa only [map_mul, AlgEquiv.apply_symm_apply] using hm

/-- Product parity is defined independently of the matrix presentation by
the native tensor product of the two canonical parity maps. -/
def tensorParityLinear :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) ≃ₗ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :=
  (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).symm.trans
    ((TensorProduct.congr
      (CliffordAlgebra.involuteEquiv (Q := q11)).toLinearEquiv θ.toLinearEquiv).trans
        (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜))

@[simp] theorem tensorParityLinear_tmul (x : CliffordAlgebra q11) (a : A) :
    tensorParityLinear 𝒜 θ (x ᵍ⊗ₜ a) = (CliffordAlgebra.involute x ᵍ⊗ₜ θ a) := rfl

private theorem tensorParity_tmul_compatible (x : CliffordAlgebra q11) (a : A) :
    tensorToMatrix 𝒜 θ hEven hOdd (tensorParityLinear 𝒜 θ (x ᵍ⊗ₜ a)) =
      matrixGrade θ.toRingEquiv (tensorToMatrix 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a)) := by
  rw [tensorParityLinear_tmul, tensorToMatrix_tmul_matrix, tensorToMatrix_tmul_matrix]
  have hx := cl11StandardEquiv_grade x
  change cl11StandardEquiv (CliffordAlgebra.involute x) = _ at hx
  rw [hx]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [map_smul]

/-- Product parity intertwines with matrix parity on every algebra element. -/
theorem tensorParity_compatible
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorToMatrix 𝒜 θ hEven hOdd (tensorParityLinear 𝒜 θ z) =
      matrixGrade θ.toRingEquiv (tensorToMatrix 𝒜 θ hEven hOdd z) := by
  obtain ⟨t, rfl⟩ :=
    (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul x a => exact tensorParity_tmul_compatible 𝒜 θ hEven hOdd x a
  | add x y hx hy => simpa only [map_add, hx, hy]

/-- The independently specified product parity preserves multiplication,
as certified by the faithful matrix presentation. -/
def tensorParity :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :=
  AlgEquiv.ofLinearEquiv (tensorParityLinear 𝒜 θ)
    (by
      apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
      simp only [tensorMatrixEquiv_apply, tensorParity_compatible, map_one])
    (by
      intro x y
      apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
      simp only [tensorMatrixEquiv_apply, tensorParity_compatible, map_mul])

@[simp] theorem tensorParity_tmul (x : CliffordAlgebra q11) (a : A) :
    tensorParity 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a) =
      (CliffordAlgebra.involute x ᵍ⊗ₜ θ a) := rfl

theorem tensorParity_involutive :
    Function.Involutive (tensorParity 𝒜 θ hEven hOdd) := by
  intro z
  apply (tensorMatrixEquiv 𝒜 θ hEven hOdd).injective
  change tensorToMatrix 𝒜 θ hEven hOdd
      (tensorParityLinear 𝒜 θ (tensorParityLinear 𝒜 θ z)) =
    tensorToMatrix 𝒜 θ hEven hOdd z
  rw [tensorParity_compatible, tensorParity_compatible]
  exact matrixGrade_involutive θ.toRingEquiv
    (coefficientParity_involutive 𝒜 θ hEven hOdd) _

/-- The actual graded module equivalence cancels the Clifford head and
retains the arbitrary noncommutative graded coefficient action. -/
def cliffordHeadCancellation :
    GradedModuleCat (tensorParity 𝒜 θ hEven hOdd).toRingEquiv ≌
      GradedModuleCat θ.toRingEquiv :=
  (ofRingEquiv (tensorParity 𝒜 θ hEven hOdd).toRingEquiv
    (matrixGrade θ.toRingEquiv) (tensorMatrixEquiv 𝒜 θ hEven hOdd).toRingEquiv
    (tensorParity_compatible 𝒜 θ hEven hOdd)).trans
      (matrixEquivalence θ.toRingEquiv).symm

/-- The coefficient embedding is the twisted diagonal, not a scalar
replacement of the residual algebra. -/
theorem tensorMatrixEquiv_tail (a : A) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd ((1 : CliffordAlgebra q11) ᵍ⊗ₜ a) =
      !![a, 0; 0, θ a] := by
  rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul, map_one, one_mul, tail_apply]

/-- The Clifford head acts by the chosen faithful standard representation. -/
theorem tensorMatrixEquiv_head (x : CliffordAlgebra q11) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ (1 : A)) = head x := by
  rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul, map_one, mul_one]

end InfoGeometry.Clifford.Cl11GradedTensorMorita
