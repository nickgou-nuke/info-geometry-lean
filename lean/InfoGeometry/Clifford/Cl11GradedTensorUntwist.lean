/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.SplitAtomDoubling.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Native graded Clifford tensor untwisting

For an arbitrary real quadratic module `Q`, the native graded tensor product
`Cl(1,1) ᵍ⊗ Cl(Q)` is isomorphic as an algebra to `Matrix (Fin 2) (Fin 2) Cl(Q)`.
The right-factor inclusion is `diag(a, involute a)`: it is the repeated diagonal
on even elements and the Klein twist on odd elements. No finite-dimensional
assumption on the coefficient Clifford algebra is used.

The proof constructs an algebra homomorphism by the native graded tensor
universal property. Bijectivity comes from an explicit linear equivalence,
using the existing real `Cl(1,1)` matrix isomorphism and Mathlib's ordinary
matrix/tensor equivalence. The two tensor multiplications are not identified.
-/

namespace InfoGeometry.Clifford.Cl11GradedTensorUntwist

open scoped TensorProduct Matrix
open SplitAtomDoubling

noncomputable section

private def hadamardChange (M : Cl11Matrix.Mat2) : Cl11Matrix.Mat2 :=
  !![(M 0 0 + M 0 1 + M 1 0 + M 1 1) / 2,
     (M 0 0 - M 0 1 + M 1 0 - M 1 1) / 2;
     (M 0 0 + M 0 1 - M 1 0 - M 1 1) / 2,
     (M 0 0 - M 0 1 - M 1 0 + M 1 1) / 2]

/-- Change from the existing real Pauli basis to the off-diagonal odd basis. -/
def offDiagonalBasisChange : Cl11Matrix.Mat2 ≃ₐ[ℝ] Cl11Matrix.Mat2 where
  toFun := hadamardChange
  invFun := hadamardChange
  left_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hadamardChange] <;> ring
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hadamardChange] <;> ring
  map_add' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hadamardChange] <;> ring
  map_mul' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamardChange, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamardChange, Matrix.algebraMap_eq_diagonal]

/-- The existing `Cl(1,1)` equivalence, expressed in the odd off-diagonal basis. -/
def offDiagonalEquiv : CliffordAlgebra Cl11Matrix.q11 ≃ₐ[ℝ] Cl11Matrix.Mat2 :=
  Cl11Matrix.cl11EquivMat.trans offDiagonalBasisChange

theorem offDiagonalEquiv_ι (v : ℝ × ℝ) :
    offDiagonalEquiv (CliffordAlgebra.ι Cl11Matrix.q11 v) =
      !![0, v.1 - v.2; v.1 + v.2, 0] := by
  change hadamardChange (Cl11Matrix.cl11ToMat
    (CliffordAlgebra.ι Cl11Matrix.q11 v)) = _
  rw [Cl11Matrix.cl11ToMat, CliffordAlgebra.lift_ι_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardChange, Cl11Matrix.gen, Cl11Matrix.Eplus, Cl11Matrix.Eminus] <;> ring

private def parityConjugation : Cl11Matrix.Mat2 ≃ₐ[ℝ] Cl11Matrix.Mat2 where
  toFun M := !![M 0 0, -M 0 1; -M 1 0, M 1 1]
  invFun M := !![M 0 0, -M 0 1; -M 1 0, M 1 1]
  left_inv M := by ext i j; fin_cases i <;> fin_cases j <;> simp
  right_inv M := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' M N := by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_mul' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_eq_diagonal]

private theorem offDiagonalEquiv_involute (a : CliffordAlgebra Cl11Matrix.q11) :
    offDiagonalEquiv (CliffordAlgebra.involute a) =
      parityConjugation (offDiagonalEquiv a) := by
  have h : offDiagonalEquiv.toAlgHom.comp CliffordAlgebra.involute =
      parityConjugation.toAlgHom.comp offDiagonalEquiv.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change offDiagonalEquiv (CliffordAlgebra.involute
      (CliffordAlgebra.ι Cl11Matrix.q11 v)) =
        parityConjugation (offDiagonalEquiv (CliffordAlgebra.ι Cl11Matrix.q11 v))
    rw [CliffordAlgebra.involute_ι, map_neg]
    simp only [offDiagonalEquiv_ι]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [parityConjugation]
  exact AlgHom.congr_fun h a

private theorem offDiagonalEquiv_even {a : CliffordAlgebra Cl11Matrix.q11}
    (ha : a ∈ CliffordAlgebra.evenOdd Cl11Matrix.q11 0) :
    offDiagonalEquiv a 0 1 = 0 ∧ offDiagonalEquiv a 1 0 = 0 := by
  have h := offDiagonalEquiv_involute a
  rw [CliffordAlgebra.involute_eq_of_mem_even ha] at h
  have h01 := congrArg (fun M : Cl11Matrix.Mat2 => M 0 1) h
  have h10 := congrArg (fun M : Cl11Matrix.Mat2 => M 1 0) h
  change offDiagonalEquiv a 0 1 = -(offDiagonalEquiv a 0 1) at h01
  change offDiagonalEquiv a 1 0 = -(offDiagonalEquiv a 1 0) at h10
  constructor
  · linarith only [h01]
  · linarith only [h10]

private theorem offDiagonalEquiv_odd {a : CliffordAlgebra Cl11Matrix.q11}
    (ha : a ∈ CliffordAlgebra.evenOdd Cl11Matrix.q11 1) :
    offDiagonalEquiv a 0 0 = 0 ∧ offDiagonalEquiv a 1 1 = 0 := by
  have h := offDiagonalEquiv_involute a
  rw [CliffordAlgebra.involute_eq_of_mem_odd ha, map_neg] at h
  have h00 := congrArg (fun M : Cl11Matrix.Mat2 => M 0 0) h
  have h11 := congrArg (fun M : Cl11Matrix.Mat2 => M 1 1) h
  change -(offDiagonalEquiv a 0 0) = offDiagonalEquiv a 0 0 at h00
  change -(offDiagonalEquiv a 1 1) = offDiagonalEquiv a 1 1 at h11
  constructor
  · linarith only [h00]
  · linarith only [h11]

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V)

/-- The parity-sensitive coefficient embedding is a genuine algebra map. -/
def gradedInsert : CliffordAlgebra Q →ₐ[ℝ] Block2 (CliffordAlgebra Q) where
  toFun a := !![a, 0; 0, CliffordAlgebra.involute a]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_eq_diagonal]

theorem gradedInsert_even {a : CliffordAlgebra Q}
    (ha : a ∈ CliffordAlgebra.evenOdd Q 0) : gradedInsert Q a = repeated a := by
  simp [gradedInsert, repeated, CliffordAlgebra.involute_eq_of_mem_even ha]

theorem gradedInsert_odd {a : CliffordAlgebra Q}
    (ha : a ∈ CliffordAlgebra.evenOdd Q 1) : gradedInsert Q a = twisted a := by
  simp [gradedInsert, twisted, CliffordAlgebra.involute_eq_of_mem_odd ha]

/-- Extend the real split atom coefficients into the coefficient Clifford algebra. -/
def outerInsert : CliffordAlgebra Cl11Matrix.q11 →ₐ[ℝ] Block2 (CliffordAlgebra Q) :=
  (Algebra.ofId ℝ (CliffordAlgebra Q)).mapMatrix.comp offDiagonalEquiv.toAlgHom

private theorem outerInsert_apply (a : CliffordAlgebra Cl11Matrix.q11) (i j : Fin 2) :
    outerInsert Q a i j = algebraMap ℝ (CliffordAlgebra Q) (offDiagonalEquiv a i j) := rfl

private theorem outerInsert_gradedInsert_commute {i j : ZMod 2}
    (a : CliffordAlgebra.evenOdd Cl11Matrix.q11 i)
    (b : CliffordAlgebra.evenOdd Q j) :
    outerInsert Q a * gradedInsert Q b =
      (-1 : ℤˣ) ^ (j * i) • (gradedInsert Q b * outerInsert Q a) := by
  have scalar_comm (r : ℝ) (x : CliffordAlgebra Q) :
      algebraMap ℝ (CliffordAlgebra Q) r * x =
        x * algebraMap ℝ (CliffordAlgebra Q) r := Algebra.commutes r x
  fin_cases j
  · rw [gradedInsert_even Q b.property]
    change outerInsert Q a * repeated (b : CliffordAlgebra Q) =
      (-1 : ℤˣ) ^ ((0 : ZMod 2) * i) •
        (repeated (b : CliffordAlgebra Q) * outerInsert Q a)
    rw [zero_mul, uzpow_zero, one_smul]
    ext u v
    fin_cases u <;> fin_cases v <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp [repeated, outerInsert_apply, scalar_comm]
  · rw [gradedInsert_odd Q b.property]
    fin_cases i
    · obtain ⟨h01, h10⟩ := offDiagonalEquiv_even a.property
      change outerInsert Q a * twisted (b : CliffordAlgebra Q) =
        (-1 : ℤˣ) ^ ((1 : ZMod 2) * 0) •
          (twisted (b : CliffordAlgebra Q) * outerInsert Q a)
      rw [mul_zero, uzpow_zero, one_smul]
      ext u v
      fin_cases u <;> fin_cases v <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp [twisted, outerInsert_apply, h01, h10, scalar_comm]
    · obtain ⟨h00, h11⟩ := offDiagonalEquiv_odd a.property
      change outerInsert Q a * twisted (b : CliffordAlgebra Q) =
        (-1 : ℤˣ) ^ ((1 : ZMod 2) * 1) •
          (twisted (b : CliffordAlgebra Q) * outerInsert Q a)
      rw [one_mul, uzpow_one, Units.neg_smul, one_smul]
      ext u v
      fin_cases u <;> fin_cases v <;>
        simp only [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp [twisted, outerInsert_apply, h00, h11, scalar_comm]

/-- The graded tensor universal property gives the untwisting algebra map. -/
def untwistHom :
    (CliffordAlgebra.evenOdd Cl11Matrix.q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q) →ₐ[ℝ]
      Block2 (CliffordAlgebra Q) :=
  GradedTensorProduct.lift _ _ (outerInsert Q) (gradedInsert Q)
    (fun {i j} a b => outerInsert_gradedInsert_commute Q (i := i) (j := j) a b)

private def columnInvolute : Block2 (CliffordAlgebra Q) ≃ₗ[ℝ]
    Block2 (CliffordAlgebra Q) where
  toFun M := !![M 0 0, CliffordAlgebra.involute (M 0 1);
                M 1 0, CliffordAlgebra.involute (M 1 1)]
  invFun M := !![M 0 0, CliffordAlgebra.involute (M 0 1);
                M 1 0, CliffordAlgebra.involute (M 1 1)]
  left_inv M := by ext i j; fin_cases i <;> fin_cases j <;> simp
  right_inv M := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' M N := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' r M := by ext i j; fin_cases i <;> fin_cases j <;> simp

private def untwistLinearEquiv :
    (CliffordAlgebra.evenOdd Cl11Matrix.q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q) ≃ₗ[ℝ]
      Block2 (CliffordAlgebra Q) :=
  (GradedTensorProduct.of ℝ _ _).symm ≪≫ₗ
    TensorProduct.congr offDiagonalEquiv.toLinearEquiv (LinearEquiv.refl ℝ _) ≪≫ₗ
    TensorProduct.comm ℝ _ _ ≪≫ₗ
    (matrixEquivTensor (Fin 2) ℝ (CliffordAlgebra Q)).symm.toLinearEquiv ≪≫ₗ
    columnInvolute Q

private theorem untwistLinearEquiv_tmul (a : CliffordAlgebra Cl11Matrix.q11)
    (b : CliffordAlgebra Q) :
    untwistLinearEquiv Q (a ᵍ⊗ₜ b) = outerInsert Q a * gradedInsert Q b := by
  have scalar_comm (r : ℝ) (x : CliffordAlgebra Q) :
      x * algebraMap ℝ (CliffordAlgebra Q) r =
        algebraMap ℝ (CliffordAlgebra Q) r * x := (Algebra.commutes r x).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [untwistLinearEquiv, GradedTensorProduct.tmul, TensorProduct.congr_tmul,
      matrixEquivTensor_apply_symm, columnInvolute, gradedInsert, outerInsert_apply,
      Matrix.mul_apply, Fin.sum_univ_two, scalar_comm]

private theorem untwistLinearEquiv_eq_hom :
    (untwistLinearEquiv Q).toLinearMap = (untwistHom Q).toLinearMap := by
  apply GradedTensorProduct.hom_ext
  apply TensorProduct.ext'
  intro a b
  exact untwistLinearEquiv_tmul Q a b

/-- Native Koszul untwisting for a real split Clifford atom and an arbitrary
real quadratic module, including infinite-dimensional modules. -/
def untwistEquiv :
    (CliffordAlgebra.evenOdd Cl11Matrix.q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q) ≃ₐ[ℝ]
      Block2 (CliffordAlgebra Q) :=
  AlgEquiv.ofBijective (untwistHom Q) (by
    have h : (untwistHom Q : _ → _) = untwistLinearEquiv Q :=
      congrArg DFunLike.coe (untwistLinearEquiv_eq_hom Q).symm
    rw [h]
    exact (untwistLinearEquiv Q).bijective)

/-- On pure tensors, untwisting is the ordered product of the two factor maps. -/
theorem untwistEquiv_tmul (a : CliffordAlgebra Cl11Matrix.q11) (b : CliffordAlgebra Q) :
    untwistEquiv Q (a ᵍ⊗ₜ b) = outerInsert Q a * gradedInsert Q b := rfl

/-- The split periodicity step as a native Clifford-algebra isomorphism. -/
def splitCliffordEquivMatrix :
    CliffordAlgebra (Cl11Matrix.q11.prod Q) ≃ₐ[ℝ] Block2 (CliffordAlgebra Q) :=
  (CliffordAlgebra.prodEquiv Cl11Matrix.q11 Q).trans (untwistEquiv Q)

theorem splitCliffordEquivMatrix_inner (v : V) :
    splitCliffordEquivMatrix Q (CliffordAlgebra.ι _ (0, v)) =
      twisted (CliffordAlgebra.ι Q v) := by
  simp [splitCliffordEquivMatrix, CliffordAlgebra.prodEquiv, untwistEquiv,
    untwistHom, GradedTensorProduct.lift_tmul, gradedInsert, twisted]

end

end InfoGeometry.Clifford.Cl11GradedTensorUntwist
