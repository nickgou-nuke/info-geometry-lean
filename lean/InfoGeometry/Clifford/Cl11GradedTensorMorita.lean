/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedMorita
import InfoGeometry.Clifford.Cl11CliffordMapIsometryBridge
import InfoGeometry.OperatorAlgebra.GradedMatrixMorita
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
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
  Algebra.commutes r a

variable (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
variable (θ : A ≃ₐ[ℝ] A)
variable (hEven : ∀ {a : A}, a ∈ 𝒜 0 → θ a = a)
variable (hOdd : ∀ {a : A}, a ∈ 𝒜 1 → θ a = -a)

include 𝒜 hEven hOdd in
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

include hEven hOdd in
omit [GradedAlgebra 𝒜] in
/-- The exact supercommutation relation needed by the native graded tensor
product. Only real head coefficients commute with the residual algebra. -/
theorem head_tail_supercommute {i j : ZMod 2}
    (x : CliffordAlgebra.evenOdd q11 i) (a : 𝒜 j) :
    head (A := A) x * tail θ a =
      (-1 : ℤˣ) ^ (j * i) • (tail θ a * head (A := A) x) := by
  fin_cases i <;> fin_cases j
  · change head (A := A) x * tail θ a =
      (-1 : ℤˣ) ^ (0 : ZMod 2) • (tail θ a * head (A := A) x)
    rw [uzpow_zero, one_smul]
    have ha := hEven a.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ← scalar_comm]
  · change head (A := A) x * tail θ a =
      (-1 : ℤˣ) ^ (0 : ZMod 2) • (tail θ a * head (A := A) x)
    rw [uzpow_zero, one_smul]
    have ha := hOdd a.property
    obtain ⟨hx01, hx10⟩ := cl11StandardEquiv_even_offDiagonal x.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hx01, hx10, ← scalar_comm]
  · change head (A := A) x * tail θ a =
      (-1 : ℤˣ) ^ (0 : ZMod 2) • (tail θ a * head (A := A) x)
    rw [uzpow_zero, one_smul]
    have ha := hEven a.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ← scalar_comm]
  · change head (A := A) x * tail θ a =
      (-1 : ℤˣ) ^ (1 : ZMod 2) • (tail θ a * head (A := A) x)
    rw [uzpow_one, Units.neg_smul, one_smul]
    have ha := hOdd a.property
    obtain ⟨hx00, hx11⟩ := cl11StandardEquiv_odd_diagonal x.property
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
        Fin.sum_univ_two, ha, hx00, hx11, ← scalar_comm]

/-- The representation is constructed by the native graded tensor lift. -/
def tensorToMatrix :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  GradedTensorProduct.lift (CliffordAlgebra.evenOdd q11) 𝒜
    (head (A := A)) (tail θ) (by
      intro i j x a
      exact head_tail_supercommute 𝒜 θ hEven hOdd x a)

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
  | add x y hx hy => simp only [map_add, hx, hy]

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
  simpa only [map_mul, AlgEquiv.apply_symm_apply,
    upperMatrixUnit, lowerMatrixUnit] using hm

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
  | add x y hx hy => simp only [map_add, hx, hy]

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

section TrivialAndInvolutionGradings

private theorem zmod2_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by revert i; decide
private theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
private theorem zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

/-- Trivial `ZMod 2` grading on an arbitrary real algebra: all elements are even (`0 ↦ ⊤`, `1 ↦ ⊥`). -/
def trivialGrading (A : Type u) [Ring A] [Algebra ℝ A] : ZMod 2 → Submodule ℝ A :=
  fun i => if i = 0 then ⊤ else ⊥

instance instGradedAlgebraTrivialGrading (A : Type u) [Ring A] [Algebra ℝ A] :
    GradedAlgebra (trivialGrading A) where
  one_mem := by simp [trivialGrading]
  mul_mem {i j} {a b} ha hb := by
    rcases zmod2_cases i with rfl | rfl <;> rcases zmod2_cases j with rfl | rfl
    · simp [trivialGrading]
    · have hb0 : b = 0 := by simpa [trivialGrading, zmod2_one_ne_zero] using hb
      simp [hb0]
    · have ha0 : a = 0 := by simpa [trivialGrading, zmod2_one_ne_zero] using ha
      simp [ha0]
    · change a * b ∈ trivialGrading A (1 + 1)
      rw [zmod2_one_add_one]
      simp [trivialGrading]
  decompose' a := DirectSum.of (fun i => trivialGrading A i) 0 ⟨a, by simp [trivialGrading]⟩
  left_inv a := by simp [DirectSum.coeAddMonoidHom_of]
  right_inv x := by
    have hzero : (DirectSum.of (fun i => trivialGrading A i) 0) ⟨0, by simp [trivialGrading]⟩ = 0 :=
      (DirectSum.of (fun i => trivialGrading A i) 0).map_zero
    have hadd : ∀ a b : A,
        (DirectSum.of (fun i => trivialGrading A i) 0) ⟨a + b, by simp [trivialGrading]⟩ =
          (DirectSum.of (fun i => trivialGrading A i) 0) ⟨a, by simp [trivialGrading]⟩ +
            (DirectSum.of (fun i => trivialGrading A i) 0) ⟨b, by simp [trivialGrading]⟩ :=
      fun a b => (DirectSum.of (fun i => trivialGrading A i) 0).map_add
        ⟨a, by simp [trivialGrading]⟩ ⟨b, by simp [trivialGrading]⟩
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact hzero
    | of i xi =>
        rcases zmod2_cases i with rfl | rfl
        · simp [DirectSum.coeAddMonoidHom_of]
        · have hx : (xi : A) = 0 := by simpa [trivialGrading, zmod2_one_ne_zero] using xi.property
          have hxi : xi = 0 := Subtype.ext hx
          rw [hxi, map_zero, map_zero]
          exact hzero
    | add x y hx hy =>
        rw [map_add]
        change (DirectSum.of (fun i => trivialGrading A i) 0)
            ⟨DirectSum.coeAddMonoidHom (trivialGrading A) x +
              DirectSum.coeAddMonoidHom (trivialGrading A) y, _⟩ = x + y
        rw [hadd]
        exact congrArg₂ (· + ·) hx hy

/-- Specialization of `tensorMatrixEquiv` to an arbitrary ungraded real algebra `A`. -/
def tensorMatrixEquivUngraded :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] trivialGrading A) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  tensorMatrixEquiv (trivialGrading A) AlgEquiv.refl
    (fun _ => rfl) (fun {a} ha => by
      have ha0 : a = 0 := by simpa [trivialGrading, zmod2_one_ne_zero] using ha
      simp [ha0])

private def ungradedTensorToMatrix :
    (CliffordAlgebra q11 ⊗[ℝ] A) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  Algebra.TensorProduct.lift (head (A := A)) (tail (AlgEquiv.refl : A ≃ₐ[ℝ] A))
    (fun x a => by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ← scalar_comm])

@[simp] private theorem ungradedTensorToMatrix_tmul (x : CliffordAlgebra q11) (a : A) :
    ungradedTensorToMatrix (x ⊗ₜ[ℝ] a) =
      !![cl11StandardEquiv x 0 0 • a, cl11StandardEquiv x 0 1 • a;
         cl11StandardEquiv x 1 0 • a, cl11StandardEquiv x 1 1 • a] := by
  change head (A := A) x * tail (AlgEquiv.refl : A ≃ₐ[ℝ] A) a = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]

private def ungradedUnitTensor (i j : Fin 2) : A →ₗ[ℝ] (CliffordAlgebra q11 ⊗[ℝ] A) :=
  TensorProduct.mk ℝ (CliffordAlgebra q11) A (headUnit i j)

private def ungradedMatrixToTensor :
    Matrix (Fin 2) (Fin 2) A →ₗ[ℝ] (CliffordAlgebra q11 ⊗[ℝ] A) :=
  (ungradedUnitTensor 0 0).comp (Matrix.entryLinearMap ℝ A 0 0) +
    (ungradedUnitTensor 0 1).comp (Matrix.entryLinearMap ℝ A 0 1) +
    (ungradedUnitTensor 1 0).comp (Matrix.entryLinearMap ℝ A 1 0) +
    (ungradedUnitTensor 1 1).comp (Matrix.entryLinearMap ℝ A 1 1)

private theorem ungradedMatrixToTensor_apply (M : Matrix (Fin 2) (Fin 2) A) :
    ungradedMatrixToTensor M =
      (headUnit 0 0 ⊗ₜ[ℝ] M 0 0) + (headUnit 0 1 ⊗ₜ[ℝ] M 0 1) +
        (headUnit 1 0 ⊗ₜ[ℝ] M 1 0) + (headUnit 1 1 ⊗ₜ[ℝ] M 1 1) := rfl

private theorem ungradedMatrixToTensor_leftInverse (z : CliffordAlgebra q11 ⊗[ℝ] A) :
    ungradedMatrixToTensor (ungradedTensorToMatrix z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul x a =>
      rw [ungradedTensorToMatrix_tmul, ungradedMatrixToTensor_apply]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
        ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
        ← TensorProduct.add_tmul, ← TensorProduct.add_tmul,
        ← TensorProduct.add_tmul, headUnit_expansion]
  | add x y hx hy => simp [hx, hy]

private theorem ungradedMatrixToTensor_rightInverse (M : Matrix (Fin 2) (Fin 2) A) :
    ungradedTensorToMatrix (ungradedMatrixToTensor M) = M := by
  rw [ungradedMatrixToTensor_apply]
  simp only [map_add, ungradedTensorToMatrix_tmul, cl11StandardEquiv_headUnit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

/-- Ungraded `Cl(1,1) ⊗[ℝ] A ≃ₐ[ℝ] M₂(A)` matching `tensorMatrixEquivUngraded`. -/
def ungradedTensorEquivMatrix :
    (CliffordAlgebra q11 ⊗[ℝ] A) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  AlgEquiv.ofBijective ungradedTensorToMatrix
    ⟨Function.LeftInverse.injective ungradedMatrixToTensor_leftInverse,
      Function.RightInverse.surjective ungradedMatrixToTensor_rightInverse⟩

@[simp] theorem ungradedTensorEquivMatrix_tmul (x : CliffordAlgebra q11) (a : A) :
    ungradedTensorEquivMatrix (x ⊗ₜ[ℝ] a) =
      !![cl11StandardEquiv x 0 0 • a, cl11StandardEquiv x 0 1 • a;
         cl11StandardEquiv x 1 0 • a, cl11StandardEquiv x 1 1 • a] :=
  ungradedTensorToMatrix_tmul x a

/-- `ZMod 2` grading on an arbitrary real algebra `A` induced by an involutive
automorphism `σ : A ≃ₐ[ℝ] A`: even = `{a | σ a = a}`, odd = `{a | σ a = -a}`. -/
def involutionGrading (σ : A ≃ₐ[ℝ] A) (_hσ : Function.Involutive σ) :
    ZMod 2 → Submodule ℝ A
  | 0 =>
    { carrier := {a : A | σ a = a}
      zero_mem' := map_zero σ
      add_mem' := fun {a b} ha hb => by
        change σ (a + b) = a + b; rw [map_add, ha, hb]
      smul_mem' := fun r {a} ha => by
        change σ (r • a) = r • a; rw [map_smul, ha] }
  | 1 =>
    { carrier := {a : A | σ a = -a}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        change σ (a + b) = -(a + b); rw [map_add, ha, hb, neg_add]
      smul_mem' := fun r {a} ha => by
        change σ (r • a) = -(r • a); rw [map_smul, ha, smul_neg] }

theorem involutionGrading_even (σ : A ≃ₐ[ℝ] A) (hσ : Function.Involutive σ)
    {a : A} (ha : a ∈ involutionGrading σ hσ 0) : σ a = a := by
  exact (ha : a ∈ involutionGrading σ hσ 0)

theorem involutionGrading_odd (σ : A ≃ₐ[ℝ] A) (hσ : Function.Involutive σ)
    {a : A} (ha : a ∈ involutionGrading σ hσ 1) : σ a = -a := by
  exact (ha : a ∈ involutionGrading σ hσ 1)

private def invEvenHom (σ : A ≃ₐ[ℝ] A) (hσ : Function.Involutive σ) :
    A →+ involutionGrading σ hσ 0 where
  toFun a :=
    ⟨(1 / 2 : ℝ) • (a + σ a), by
      change σ ((1 / 2 : ℝ) • (a + σ a)) = (1 / 2 : ℝ) • (a + σ a)
      rw [map_smul, map_add, hσ a, add_comm]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • (a + b + σ (a + b)) =
      (1 / 2 : ℝ) • (a + σ a) + (1 / 2 : ℝ) • (b + σ b)
    rw [map_add, ← smul_add]
    congr 1; abel

private def invOddHom (σ : A ≃ₐ[ℝ] A) (hσ : Function.Involutive σ) :
    A →+ involutionGrading σ hσ 1 where
  toFun a :=
    ⟨(1 / 2 : ℝ) • (a - σ a), by
      change σ ((1 / 2 : ℝ) • (a - σ a)) = -((1 / 2 : ℝ) • (a - σ a))
      rw [map_smul, map_sub, hσ a, ← smul_neg, neg_sub]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • (a + b - σ (a + b)) =
      (1 / 2 : ℝ) • (a - σ a) + (1 / 2 : ℝ) • (b - σ b)
    rw [map_add, ← smul_add]
    congr 1; abel

private def invDecomposeAdd (σ : A ≃ₐ[ℝ] A) (hσ : Function.Involutive σ) :
    A →+ DirectSum (ZMod 2) (fun i => involutionGrading σ hσ i) :=
  (DirectSum.of (fun i => involutionGrading σ hσ i) 0).comp (invEvenHom σ hσ) +
    (DirectSum.of (fun i => involutionGrading σ hσ i) 1).comp (invOddHom σ hσ)

instance instGradedAlgebraInvolutionGrading (σ : A ≃ₐ[ℝ] A)
    (hσ : Function.Involutive σ) : GradedAlgebra (involutionGrading σ hσ) where
  one_mem := map_one σ
  mul_mem {i j} {a b} ha hb := by
    rcases zmod2_cases i with rfl | rfl <;> rcases zmod2_cases j with rfl | rfl
    · change σ (a * b) = a * b
      rw [map_mul, involutionGrading_even σ hσ ha, involutionGrading_even σ hσ hb]
    · change σ (a * b) = -(a * b)
      rw [map_mul, involutionGrading_even σ hσ ha, involutionGrading_odd σ hσ hb, mul_neg]
    · change σ (a * b) = -(a * b)
      rw [map_mul, involutionGrading_odd σ hσ ha, involutionGrading_even σ hσ hb, neg_mul]
    · change σ (a * b) = a * b
      rw [map_mul, involutionGrading_odd σ hσ ha, involutionGrading_odd σ hσ hb, neg_mul_neg]
  decompose' := invDecomposeAdd σ hσ
  left_inv a := by
    change DirectSum.coeAddMonoidHom (involutionGrading σ hσ) (invDecomposeAdd σ hσ a) = a
    dsimp [invDecomposeAdd]
    rw [map_add, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    change (1 / 2 : ℝ) • (a + σ a) + (1 / 2 : ℝ) • (a - σ a) = a
    rw [← smul_add, show (a + σ a) + (a - σ a) = (2 : ℝ) • a by rw [two_smul]; abel,
      smul_smul]
    norm_num
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp [map_zero]
    | of i xi =>
        rcases zmod2_cases i with rfl | rfl
        · have he : σ (xi : A) = xi := involutionGrading_even σ hσ xi.property
          have hsub0 : invEvenHom σ hσ (xi : A) = xi := by
            apply Subtype.ext
            change (1 / 2 : ℝ) • ((xi : A) + σ xi) = xi
            rw [he, ← two_smul ℝ, smul_smul]; norm_num
          have hsub1 : invOddHom σ hσ (xi : A) = 0 := by
            apply Subtype.ext
            change (1 / 2 : ℝ) • ((xi : A) - σ xi) = 0
            rw [he, sub_self, smul_zero]
          dsimp [invDecomposeAdd]
          rw [DirectSum.coeAddMonoidHom_of, hsub0, hsub1, map_zero, add_zero]
        · have ho : σ (xi : A) = -xi := involutionGrading_odd σ hσ xi.property
          have hsub0 : invEvenHom σ hσ (xi : A) = 0 := by
            apply Subtype.ext
            change (1 / 2 : ℝ) • ((xi : A) + σ xi) = 0
            rw [ho, add_neg_cancel, smul_zero]
          have hsub1 : invOddHom σ hσ (xi : A) = xi := by
            apply Subtype.ext
            change (1 / 2 : ℝ) • ((xi : A) - σ xi) = xi
            rw [ho, sub_neg_eq_add, ← two_smul ℝ, smul_smul]; norm_num
          dsimp [invDecomposeAdd]
          rw [DirectSum.coeAddMonoidHom_of, hsub0, hsub1, map_zero, zero_add]
    | add x y hx hy =>
        rw [map_add, (invDecomposeAdd σ hσ).map_add, hx, hy]

/-- `matrixGrade` upgraded to an `ℝ`-algebra equivalence. -/
def matrixAlgGrade (σ : A ≃ₐ[ℝ] A) :
    Matrix (Fin 2) (Fin 2) A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A where
  __ := matrixGrade σ.toRingEquiv
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one, map_smul]

@[simp] theorem matrixAlgGrade_apply (σ : A ≃ₐ[ℝ] A) (M : Matrix (Fin 2) (Fin 2) A) :
    matrixAlgGrade σ M = !![σ (M 0 0), -σ (M 0 1); -σ (M 1 0), σ (M 1 1)] := rfl

theorem matrixAlgGrade_involutive (σ : A ≃ₐ[ℝ] A) (hσ : Function.Involutive σ) :
    Function.Involutive (matrixAlgGrade σ) :=
  matrixGrade_involutive σ.toRingEquiv hσ

/-- The canonical even corner projector `(1 + J1_cl) / 2` in `Cl(1,1)`. -/
def pPlus : CliffordAlgebra q11 := (1 / 2 : ℝ) • (1 + J1_cl)

theorem pPlus_mem_even : pPlus ∈ CliffordAlgebra.evenOdd q11 0 := by
  have h1 : (1 : CliffordAlgebra q11) ∈ CliffordAlgebra.evenOdd q11 0 :=
    SetLike.GradedOne.one_mem
  have hJ : J1_cl ∈ CliffordAlgebra.evenOdd q11 0 := by
    change CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1) ∈
      CliffordAlgebra.evenOdd q11 0
    rw [← zmod2_one_add_one]
    exact SetLike.GradedMul.mul_mem (CliffordAlgebra.ι_mem_evenOdd_one q11 (1, 0))
      (CliffordAlgebra.ι_mem_evenOdd_one q11 (0, 1))
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 hJ)

theorem pPlus_sq : pPlus * pPlus = pPlus := by
  dsimp [pPlus]
  rw [smul_mul_smul_comm]
  have hmul : (1 + J1_cl) * (1 + J1_cl) = (2 : ℝ) • (1 + J1_cl) := by
    simp only [add_mul, mul_add, one_mul, mul_one, J1_cl_sq, two_smul]
    abel
  rw [hmul, smul_smul]
  norm_num

@[simp] theorem cl11StandardEquiv_pPlus :
    cl11StandardEquiv pPlus = Matrix.single 0 0 1 := by
  dsimp [pPlus]
  rw [map_smul, map_add, map_one, cl11StandardEquiv_J1_cl]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Eplus, Matrix.single]; try norm_num)

/-- For any `(𝒜, θ)` on `A` (without assuming parity on `a`), `pPlus ᵍ⊗ₜ a`
maps directly to the `(0,0)` corner matrix `!![a, 0; 0, 0]`. -/
theorem tensorMatrixEquiv_pPlus_tmul (a : A) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd (pPlus ᵍ⊗ₜ a) = !![a, 0; 0, 0] := by
  rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix, cl11StandardEquiv_pPlus]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

end TrivialAndInvolutionGradings

section HeadSymmetryLift

private theorem q11_involute_eq_self_iff_mem_even (x : CliffordAlgebra q11) :
    CliffordAlgebra.involute x = x ↔ x ∈ CliffordAlgebra.evenOdd q11 0 := by
  constructor
  · intro hfix
    obtain ⟨e, o, heo, _⟩ :=
      Submodule.existsUnique_add_of_isCompl (CliffordAlgebra.evenOdd_isCompl (Q := q11)) x
    have hinvol : CliffordAlgebra.involute x = (e : CliffordAlgebra q11) - o := by
      rw [← heo, map_add, CliffordAlgebra.involute_eq_of_mem_even e.property,
        CliffordAlgebra.involute_eq_of_mem_odd o.property, sub_eq_add_neg]
    have hsum : (e : CliffordAlgebra q11) + o = (e : CliffordAlgebra q11) - o :=
      heo.trans (hfix.symm.trans hinvol)
    have honeg : (o : CliffordAlgebra q11) = -o :=
      add_left_cancel (by simpa only [sub_eq_add_neg] using hsum)
    have hozero : (o : CliffordAlgebra q11) = 0 := by
      have htwo : (2 : ℝ) • (o : CliffordAlgebra q11) = 0 := by
        rw [two_smul]; nth_rw 2 [honeg]; exact add_neg_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [← heo, hozero, add_zero]
    exact e.property
  · exact CliffordAlgebra.involute_eq_of_mem_even

private theorem q11_involute_eq_neg_iff_mem_odd (x : CliffordAlgebra q11) :
    CliffordAlgebra.involute x = -x ↔ x ∈ CliffordAlgebra.evenOdd q11 1 := by
  constructor
  · intro hneg
    obtain ⟨e, o, heo, _⟩ :=
      Submodule.existsUnique_add_of_isCompl (CliffordAlgebra.evenOdd_isCompl (Q := q11)) x
    have hinvol : CliffordAlgebra.involute x = (e : CliffordAlgebra q11) - o := by
      rw [← heo, map_add, CliffordAlgebra.involute_eq_of_mem_even e.property,
        CliffordAlgebra.involute_eq_of_mem_odd o.property, sub_eq_add_neg]
    have hneg_e : (e : CliffordAlgebra q11) = -(e : CliffordAlgebra q11) := by
      have hsum : (e : CliffordAlgebra q11) - o = -((e : CliffordAlgebra q11) + o) :=
        hinvol.symm.trans (hneg.trans (congrArg Neg.neg heo.symm))
      exact add_right_cancel (by simpa only [sub_eq_add_neg, neg_add] using hsum)
    have hezero : (e : CliffordAlgebra q11) = 0 := by
      have htwo : (2 : ℝ) • (e : CliffordAlgebra q11) = 0 := by
        rw [two_smul]; nth_rw 2 [hneg_e]; exact add_neg_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [← heo, hezero, zero_add]
    exact o.property
  · exact CliffordAlgebra.involute_eq_of_mem_odd

/-- Any `ℝ`-algebra endomorphism of `CliffordAlgebra q11` commuting with
`CliffordAlgebra.involute` preserves the `ZMod 2` grading `evenOdd q11`. -/
theorem involute_comm_mem_evenOdd
    (φ : CliffordAlgebra q11 →ₐ[ℝ] CliffordAlgebra q11)
    (hφ : ∀ x, φ (CliffordAlgebra.involute x) = CliffordAlgebra.involute (φ x))
    (i : ZMod 2) {x : CliffordAlgebra q11}
    (hx : x ∈ CliffordAlgebra.evenOdd q11 i) :
    φ x ∈ CliffordAlgebra.evenOdd q11 i := by
  fin_cases i
  · apply (q11_involute_eq_self_iff_mem_even _).mp
    rw [← hφ, CliffordAlgebra.involute_eq_of_mem_even hx]
  · apply (q11_involute_eq_neg_iff_mem_odd _).mp
    rw [← hφ, CliffordAlgebra.involute_eq_of_mem_odd hx, map_neg]

private theorem clifford_involute_comm_of_isometry
    (f : q11.IsometryEquiv q11) (x : CliffordAlgebra q11) :
    CliffordAlgebra.equivOfIsometry f (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (CliffordAlgebra.equivOfIsometry f x) := by
  have hhom :
      (CliffordAlgebra.equivOfIsometry f).toAlgHom.comp (CliffordAlgebra.involute (Q := q11)) =
        (CliffordAlgebra.involute (Q := q11)).comp (CliffordAlgebra.equivOfIsometry f).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change CliffordAlgebra.map f.toIsometry (CliffordAlgebra.involute (CliffordAlgebra.ι q11 v)) =
      CliffordAlgebra.involute (CliffordAlgebra.map f.toIsometry (CliffordAlgebra.ι q11 v))
    simp [CliffordAlgebra.involute_ι, CliffordAlgebra.map_apply_ι]
  exact AlgHom.congr_fun hhom x

/-- Lift a grading-preserving endomorphism of the `Cl(1,1)` head onto `evenOdd q11 ᵍ⊗[ℝ] 𝒜`. -/
def headLiftAlgHom
    (φ : CliffordAlgebra q11 →ₐ[ℝ] CliffordAlgebra q11)
    (hφ : ∀ x, φ (CliffordAlgebra.involute x) = CliffordAlgebra.involute (φ x)) :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) →ₐ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :=
  GradedTensorProduct.lift (CliffordAlgebra.evenOdd q11) 𝒜
    ((GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd q11) 𝒜).comp φ)
    (GradedTensorProduct.includeRight (CliffordAlgebra.evenOdd q11) 𝒜)
    (by
      intro i j x a
      change ((φ (x : CliffordAlgebra q11) ᵍ⊗ₜ (1 : A)) *
          ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (a : A))) =
        (-1 : ℤˣ) ^ (j * i) •
          (((1 : CliffordAlgebra q11) ᵍ⊗ₜ (a : A)) *
            (φ (x : CliffordAlgebra q11) ᵍ⊗ₜ (1 : A)))
      have hxφ : φ (x : CliffordAlgebra q11) ∈ CliffordAlgebra.evenOdd q11 i :=
        involute_comm_mem_evenOdd φ hφ i x.property
      have hL : (φ (x : CliffordAlgebra q11) ᵍ⊗ₜ (1 : A)) *
          ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (a : A)) =
          (φ (x : CliffordAlgebra q11) ᵍ⊗ₜ (a : A)) :=
        GradedTensorProduct.tmul_one_mul_one_tmul (CliffordAlgebra.evenOdd q11) 𝒜 _ _
      have hR : ((1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] (a : A) :
            CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) *
          (φ (x : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] (1 : A)) =
          (-1 : ℤˣ) ^ (j * i) • (φ (x : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] (a : A)) := by
        have h := GradedTensorProduct.tmul_coe_mul_coe_tmul
          (CliffordAlgebra.evenOdd q11) 𝒜 (1 : CliffordAlgebra q11) a
          ⟨φ (x : CliffordAlgebra q11), hxφ⟩ (1 : A)
        simpa [one_mul, mul_one] using h
      rw [hL, hR, smul_smul, Int.units_mul_self, one_smul])

@[simp] theorem headLiftAlgHom_tmul
    (φ : CliffordAlgebra q11 →ₐ[ℝ] CliffordAlgebra q11)
    (hφ : ∀ x, φ (CliffordAlgebra.involute x) = CliffordAlgebra.involute (φ x))
    (x : CliffordAlgebra q11) (a : A) :
    headLiftAlgHom 𝒜 φ hφ (x ᵍ⊗ₜ a) = (φ x ᵍ⊗ₜ a) :=
  GradedTensorProduct.tmul_one_mul_one_tmul (CliffordAlgebra.evenOdd q11) 𝒜 (φ x) a

/-- Lift a grading-preserving automorphism of the `Cl(1,1)` head onto `evenOdd q11 ᵍ⊗[ℝ] 𝒜`. -/
def headLiftAlgEquiv
    (φ : CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11)
    (hφ : ∀ x, φ (CliffordAlgebra.involute x) = CliffordAlgebra.involute (φ x)) :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :=
  let hφ' : ∀ x, φ.toAlgHom (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (φ.toAlgHom x) := hφ
  let hφ_symm : ∀ x, φ.symm.toAlgHom (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (φ.symm.toAlgHom x) := fun x => by
    apply φ.injective
    change φ (φ.symm (CliffordAlgebra.involute x)) =
      φ (CliffordAlgebra.involute (φ.symm x))
    rw [φ.apply_symm_apply, hφ, φ.apply_symm_apply]
  AlgEquiv.ofAlgHom
    (headLiftAlgHom 𝒜 φ.toAlgHom hφ')
    (headLiftAlgHom 𝒜 φ.symm.toAlgHom hφ_symm)
    (by
      apply GradedTensorProduct.algHom_ext (𝒜 := CliffordAlgebra.evenOdd q11) (ℬ := 𝒜)
      · apply AlgHom.ext; intro x
        change headLiftAlgHom 𝒜 φ.toAlgHom hφ'
            (headLiftAlgHom 𝒜 φ.symm.toAlgHom hφ_symm (x ᵍ⊗ₜ 1)) = (x ᵍ⊗ₜ 1)
        rw [headLiftAlgHom_tmul, headLiftAlgHom_tmul]
        exact congrArg (· ᵍ⊗ₜ[ℝ] (1 : A)) (φ.apply_symm_apply x)
      · apply AlgHom.ext; intro a
        change headLiftAlgHom 𝒜 φ.toAlgHom hφ'
            (headLiftAlgHom 𝒜 φ.symm.toAlgHom hφ_symm (1 ᵍ⊗ₜ a)) = (1 ᵍ⊗ₜ a)
        rw [headLiftAlgHom_tmul, headLiftAlgHom_tmul, map_one, map_one])
    (by
      apply GradedTensorProduct.algHom_ext (𝒜 := CliffordAlgebra.evenOdd q11) (ℬ := 𝒜)
      · apply AlgHom.ext; intro x
        change headLiftAlgHom 𝒜 φ.symm.toAlgHom hφ_symm
            (headLiftAlgHom 𝒜 φ.toAlgHom hφ' (x ᵍ⊗ₜ 1)) = (x ᵍ⊗ₜ 1)
        rw [headLiftAlgHom_tmul, headLiftAlgHom_tmul]
        exact congrArg (· ᵍ⊗ₜ[ℝ] (1 : A)) (φ.symm_apply_apply x)
      · apply AlgHom.ext; intro a
        change headLiftAlgHom 𝒜 φ.symm.toAlgHom hφ_symm
            (headLiftAlgHom 𝒜 φ.toAlgHom hφ' (1 ᵍ⊗ₜ a)) = (1 ᵍ⊗ₜ a)
        rw [headLiftAlgHom_tmul, headLiftAlgHom_tmul, map_one, map_one])

@[simp] theorem headLiftAlgEquiv_tmul
    (φ : CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11)
    (hφ : ∀ x, φ (CliffordAlgebra.involute x) = CliffordAlgebra.involute (φ x))
    (x : CliffordAlgebra q11) (a : A) :
    headLiftAlgEquiv 𝒜 φ hφ (x ᵍ⊗ₜ a) = (φ x ᵍ⊗ₜ a) :=
  headLiftAlgHom_tmul 𝒜 φ.toAlgHom hφ x a

/-- Package a grading-preserving group action on the `Cl(1,1)` head as a
`SymmetryAction` on `evenOdd q11 ᵍ⊗[ℝ] 𝒜`. -/
def headLiftSymmetryAction {G : Type*} [Group G]
    (φ : G →* (CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11))
    (hφ : ∀ g x, φ g (CliffordAlgebra.involute x) = CliffordAlgebra.involute (φ g x)) :
    InfoGeometry.OperatorAlgebra.SymmetryAction G (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) where
  act g := (headLiftAlgEquiv 𝒜 (φ g) (hφ g)).toRingEquiv
  act_one z := by
    obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
    induction t using TensorProduct.inductionOn with
    | tmul x a =>
        change headLiftAlgEquiv 𝒜 (φ 1) (hφ 1) (x ᵍ⊗ₜ a) = (x ᵍ⊗ₜ a)
        rw [headLiftAlgEquiv_tmul, map_one]
        rfl
    | add x y hx hy =>
        simp only [map_add] at hx hy ⊢
        rw [hx, hy]
  act_mul g h z := by
    obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
    induction t using TensorProduct.inductionOn with
    | tmul x a =>
        change headLiftAlgEquiv 𝒜 (φ (g * h)) (hφ (g * h)) (x ᵍ⊗ₜ a) =
          headLiftAlgEquiv 𝒜 (φ g) (hφ g)
            (headLiftAlgEquiv 𝒜 (φ h) (hφ h) (x ᵍ⊗ₜ a))
        rw [headLiftAlgEquiv_tmul, headLiftAlgEquiv_tmul, headLiftAlgEquiv_tmul, map_mul]
        rfl
    | add x y hx hy =>
        simp only [map_add] at hx hy ⊢
        rw [hx, hy]

/-- Conjugation on `M₂(A)` by a scalar-extended unit `u : M₂(ℝ)ˣ`. -/
def matrixScalarAdjoint (u : Mat2ˣ) :
    Matrix (Fin 2) (Fin 2) A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  let uA : (Matrix (Fin 2) (Fin 2) A)ˣ :=
    Units.map (Algebra.ofId ℝ A).mapMatrix.toMonoidHom u
  { toFun := fun M => (uA : Matrix (Fin 2) (Fin 2) A) * M * (↑(uA⁻¹) : Matrix (Fin 2) (Fin 2) A)
    invFun := fun M => (↑(uA⁻¹) : Matrix (Fin 2) (Fin 2) A) * M * (uA : Matrix (Fin 2) (Fin 2) A)
    left_inv := fun M => by simp [mul_assoc]
    right_inv := fun M => by simp [mul_assoc]
    map_mul' := fun M N => by simp [mul_assoc]
    map_add' := fun M N => by simp [mul_add, add_mul]
    commutes' := fun r => by
      have hcomm : algebraMap ℝ (Matrix (Fin 2) (Fin 2) A) r * (uA : Matrix (Fin 2) (Fin 2) A) =
          (uA : Matrix (Fin 2) (Fin 2) A) * algebraMap ℝ (Matrix (Fin 2) (Fin 2) A) r := by
        ext i j
        simp [Algebra.algebraMap_eq_smul_one]
      rw [← hcomm, mul_assoc, Units.mul_inv, mul_one] }

@[simp] theorem matrixScalarAdjoint_apply (u : Mat2ˣ) (M : Matrix (Fin 2) (Fin 2) A) :
    matrixScalarAdjoint (A := A) u M =
      (u : Mat2).map (algebraMap ℝ A) * M * ((↑(u⁻¹) : Mat2).map (algebraMap ℝ A)) := rfl

private theorem eminus_mul_neg_eminus_local : Eminus * (-Eminus) = (1 : Mat2) := by
  rw [mul_neg, Eminus_sq]
  simp

private theorem cl11StandardEquiv_splitReflection (x : CliffordAlgebra q11) :
    cl11StandardEquiv (splitReflectionCliffordAuto x) = J1 * cl11StandardEquiv x * J1 := by
  let uJ1 : Mat2ˣ := Units.mkOfMulEqOne J1 J1 J1_sq
  have hj : (uJ1 : Mat2) = J1 := rfl
  have hjinv : (↑(uJ1⁻¹) : Mat2) = J1 := rfl
  have hhom :
      cl11StandardEquiv.toAlgHom.comp splitReflectionCliffordAuto.toAlgHom =
        (matrixScalarAdjoint (A := ℝ) uJ1).toAlgHom.comp cl11StandardEquiv.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    rcases v with ⟨x₁, x₂⟩
    change cl11StandardEquiv (splitReflectionCliffordAuto (CliffordAlgebra.ι q11 (x₁, x₂))) =
      matrixScalarAdjoint (A := ℝ) uJ1 (cl11StandardEquiv (CliffordAlgebra.ι q11 (x₁, x₂)))
    rw [splitReflectionCliffordAuto_ι, cl11StandardEquiv_ι, cl11StandardEquiv_ι,
      matrixScalarAdjoint_apply, hj, hjinv]
    simp only [Algebra.algebraMap_self, splitReflection]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two]
  have h := AlgHom.congr_fun hhom x
  change cl11StandardEquiv (splitReflectionCliffordAuto x) =
    matrixScalarAdjoint (A := ℝ) uJ1 (cl11StandardEquiv x) at h
  rw [matrixScalarAdjoint_apply, hj, hjinv] at h
  simpa [Algebra.algebraMap_self] using h

private theorem cl11StandardEquiv_splitReflectionFirstCoordinate (x : CliffordAlgebra q11) :
    cl11StandardEquiv (splitReflectionFirstCoordinateCliffordAuto x) =
      Eminus * cl11StandardEquiv x * (-Eminus) := by
  let uEm : Mat2ˣ := Units.mkOfMulEqOne Eminus (-Eminus) eminus_mul_neg_eminus_local
  have he : (uEm : Mat2) = Eminus := rfl
  have heinv : (↑(uEm⁻¹) : Mat2) = -Eminus := rfl
  have hhom :
      cl11StandardEquiv.toAlgHom.comp splitReflectionFirstCoordinateCliffordAuto.toAlgHom =
        (matrixScalarAdjoint (A := ℝ) uEm).toAlgHom.comp cl11StandardEquiv.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    rcases v with ⟨x₁, x₂⟩
    change cl11StandardEquiv
        (splitReflectionFirstCoordinateCliffordAuto (CliffordAlgebra.ι q11 (x₁, x₂))) =
      matrixScalarAdjoint (A := ℝ) uEm
        (cl11StandardEquiv (CliffordAlgebra.ι q11 (x₁, x₂)))
    rw [splitReflectionFirstCoordinateCliffordAuto_ι, cl11StandardEquiv_ι,
      cl11StandardEquiv_ι, matrixScalarAdjoint_apply, he, heinv]
    simp only [Algebra.algebraMap_self, splitReflectionFirstCoordinate]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have h := AlgHom.congr_fun hhom x
  change cl11StandardEquiv (splitReflectionFirstCoordinateCliffordAuto x) =
    matrixScalarAdjoint (A := ℝ) uEm (cl11StandardEquiv x) at h
  rw [matrixScalarAdjoint_apply, he, heinv] at h
  simpa [Algebra.algebraMap_self] using h

/-- Under `tensorMatrixEquiv`, lifting `CliffordAlgebra.involuteEquiv` on the `Cl(1,1)`
head intertwines with untwisted conjugation by `Eplus`. -/
theorem tensorMatrixEquiv_headLift_involute
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd
        (headLiftAlgEquiv 𝒜 CliffordAlgebra.involuteEquiv (fun _ => rfl) z) =
      matrixScalarAdjoint (A := A) (Units.mkOfMulEqOne Eplus Eplus Eplus_sq)
        (tensorMatrixEquiv 𝒜 θ hEven hOdd z) := by
  let uEp : Mat2ˣ := Units.mkOfMulEqOne Eplus Eplus Eplus_sq
  have hep : (uEp : Mat2) = Eplus := rfl
  have hepinv : (↑(uEp⁻¹) : Mat2) = Eplus := rfl
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
      have hhead : headLiftAlgEquiv 𝒜 CliffordAlgebra.involuteEquiv (fun _ => rfl)
          ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜) (x ⊗ₜ[ℝ] a)) =
          (CliffordAlgebra.involute x ᵍ⊗ₜ a) :=
        headLiftAlgEquiv_tmul 𝒜 CliffordAlgebra.involuteEquiv (fun _ => rfl) x a
      rw [hhead]
      change tensorMatrixEquiv 𝒜 θ hEven hOdd (CliffordAlgebra.involute x ᵍ⊗ₜ a) =
        matrixScalarAdjoint (A := A) uEp (tensorMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a))
      rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
        tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
        cl11StandardEquiv_involute, matrixScalarAdjoint_apply, hep, hepinv]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Eplus, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
          Fin.sum_univ_two, Algebra.smul_def]
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      rw [hx, hy]

/-- Under `tensorMatrixEquiv`, lifting `splitReflectionCliffordAuto` on the `Cl(1,1)` head
intertwines with `θ`-entrywise-twisted conjugation by `J1`. -/
theorem tensorMatrixEquiv_headLift_splitReflection
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd
        (headLiftAlgEquiv 𝒜 splitReflectionCliffordAuto
          (clifford_involute_comm_of_isometry splitReflectionIsometryEquiv) z) =
      matrixScalarAdjoint (A := A) (Units.mkOfMulEqOne J1 J1 J1_sq)
        ((tensorMatrixEquiv 𝒜 θ hEven hOdd z).map θ) := by
  have hθ := coefficientParity_involutive 𝒜 θ hEven hOdd
  let uJ1 : Mat2ˣ := Units.mkOfMulEqOne J1 J1 J1_sq
  have hj : (uJ1 : Mat2) = J1 := rfl
  have hjinv : (↑(uJ1⁻¹) : Mat2) = J1 := rfl
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
      have hhead : headLiftAlgEquiv 𝒜 splitReflectionCliffordAuto
          (clifford_involute_comm_of_isometry splitReflectionIsometryEquiv)
          ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜) (x ⊗ₜ[ℝ] a)) =
          (splitReflectionCliffordAuto x ᵍ⊗ₜ a) :=
        headLiftAlgEquiv_tmul 𝒜 splitReflectionCliffordAuto _ x a
      rw [hhead]
      change tensorMatrixEquiv 𝒜 θ hEven hOdd (splitReflectionCliffordAuto x ᵍ⊗ₜ a) =
        matrixScalarAdjoint (A := A) uJ1 ((tensorMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a)).map θ)
      rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
        tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
        cl11StandardEquiv_splitReflection, matrixScalarAdjoint_apply, hj, hjinv]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [J1, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two,
          hθ a, Algebra.smul_def]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, ← map_add (matrixScalarAdjoint (A := A) uJ1)]
      congr 1; ext i j; simp

/-- Under `tensorMatrixEquiv`, lifting `splitReflectionFirstCoordinateCliffordAuto` on the
`Cl(1,1)` head intertwines with `θ`-entrywise-twisted conjugation by `Eminus`. -/
theorem tensorMatrixEquiv_headLift_splitReflectionFirstCoordinate
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd
        (headLiftAlgEquiv 𝒜 splitReflectionFirstCoordinateCliffordAuto
          (clifford_involute_comm_of_isometry
            splitReflectionFirstCoordinateIsometryEquiv) z) =
      matrixScalarAdjoint (A := A)
        (Units.mkOfMulEqOne Eminus (-Eminus) eminus_mul_neg_eminus_local)
        ((tensorMatrixEquiv 𝒜 θ hEven hOdd z).map θ) := by
  have hθ := coefficientParity_involutive 𝒜 θ hEven hOdd
  let uEm : Mat2ˣ := Units.mkOfMulEqOne Eminus (-Eminus) eminus_mul_neg_eminus_local
  have he : (uEm : Mat2) = Eminus := rfl
  have heinv : (↑(uEm⁻¹) : Mat2) = -Eminus := rfl
  obtain ⟨t, rfl⟩ := (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜).surjective z
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
      have hhead : headLiftAlgEquiv 𝒜 splitReflectionFirstCoordinateCliffordAuto
          (clifford_involute_comm_of_isometry
            splitReflectionFirstCoordinateIsometryEquiv)
          ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11) 𝒜) (x ⊗ₜ[ℝ] a)) =
          (splitReflectionFirstCoordinateCliffordAuto x ᵍ⊗ₜ a) :=
        headLiftAlgEquiv_tmul 𝒜 splitReflectionFirstCoordinateCliffordAuto _ x a
      rw [hhead]
      change tensorMatrixEquiv 𝒜 θ hEven hOdd
          (splitReflectionFirstCoordinateCliffordAuto x ᵍ⊗ₜ a) =
        matrixScalarAdjoint (A := A) uEm ((tensorMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a)).map θ)
      rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
        tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
        cl11StandardEquiv_splitReflectionFirstCoordinate, matrixScalarAdjoint_apply, he, heinv]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Eminus, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two,
          hθ a, Algebra.smul_def, neg_mul, mul_neg]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, ← map_add (matrixScalarAdjoint (A := A) uEm)]
      congr 1; ext i j; simp

/-- Dual untwisted matrix conjugation `J1 * M * J1` corresponds to twisting *both*
the `Cl(1,1)` head by `splitReflectionCliffordAuto` and the residual algebra `A` by `θ`. -/
theorem tensorMatrixEquiv_splitReflection_tmul_parity (x : CliffordAlgebra q11) (a : A) :
    tensorMatrixEquiv 𝒜 θ hEven hOdd (splitReflectionCliffordAuto x ᵍ⊗ₜ θ a) =
      matrixScalarAdjoint (A := A) (Units.mkOfMulEqOne J1 J1 J1_sq)
        (tensorMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a)) := by
  have hθ := coefficientParity_involutive 𝒜 θ hEven hOdd
  let uJ1 : Mat2ˣ := Units.mkOfMulEqOne J1 J1 J1_sq
  have hj : (uJ1 : Mat2) = J1 := rfl
  have hjinv : (↑(uJ1⁻¹) : Mat2) = J1 := rfl
  change _ = matrixScalarAdjoint (A := A) uJ1 (tensorMatrixEquiv 𝒜 θ hEven hOdd (x ᵍ⊗ₜ a))
  rw [tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
    tensorMatrixEquiv_apply, tensorToMatrix_tmul_matrix,
    cl11StandardEquiv_splitReflection, matrixScalarAdjoint_apply, hj, hjinv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [J1, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two,
      hθ a, Algebra.smul_def]

end HeadSymmetryLift

end InfoGeometry.Clifford.Cl11GradedTensorMorita
