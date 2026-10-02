import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.ChiralStokesPauliBasis
import InfoGeometry.Canonical.ChiralStokesPauliRelations

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetKreinAdjoint

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetStokesCoordinates
open InfoGeometry.Canonical.ChiralStokesPauliBasis

def kreinSymmetry : M6C :=
  sheetTensor sheetFlip (1 : M3C)

def kreinAdjoint (A : M6C) : M6C :=
  kreinSymmetry * star A * kreinSymmetry

def stokesKreinAdjoint (q : StokesQuad) : StokesQuad :=
  (star q.1, (star q.2.1, (-star q.2.2.1, -star q.2.2.2)))

lemma sheetTensor_mul (P Q : SheetMatrix) (A B : M3C) :
    sheetTensor P A * sheetTensor Q B =
      sheetTensor (P * Q) (A * B) := by
  change Matrix.kronecker P A * Matrix.kronecker Q B =
    Matrix.kronecker (P * Q) (A * B)
  exact (Matrix.mul_kronecker_mul P Q A B).symm

lemma sheetTensor_identity :
    sheetTensor sheetIdentity (1 : M3C) = (1 : M6C) := by
  ext ⟨s, i⟩ ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [sheetTensor, sheetIdentity, Matrix.one_apply,
      Matrix.mul_apply, Fin.sum_univ_succ, eq_comm]

theorem kreinSymmetry_star :
    star kreinSymmetry = kreinSymmetry := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases s <;> fin_cases t <;>
    simp [kreinSymmetry, sheetTensor, sheetFlip, Matrix.star_apply,
      Matrix.one_apply, eq_comm]

theorem kreinSymmetry_sq :
    kreinSymmetry * kreinSymmetry = (1 : M6C) := by
  rw [kreinSymmetry, sheetTensor_mul, sheetFlip_sq]
  simpa using sheetTensor_identity

theorem kreinAdjoint_involutive (A : M6C) :
    kreinAdjoint (kreinAdjoint A) = A := by
  unfold kreinAdjoint
  simp only [Matrix.star_mul, star_star, kreinSymmetry_star, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc, kreinSymmetry_sq, Matrix.one_mul, Matrix.mul_one]

theorem kreinAdjoint_mul (A B : M6C) :
    kreinAdjoint (A * B) = kreinAdjoint B * kreinAdjoint A := by
  unfold kreinAdjoint
  simp only [Matrix.star_mul, kreinSymmetry_star, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, kreinSymmetry_sq, Matrix.one_mul,
    Matrix.mul_one]

theorem kreinAdjoint_add (A B : M6C) :
    kreinAdjoint (A + B) = kreinAdjoint A + kreinAdjoint B := by
  simp [kreinAdjoint, star_add, add_mul, mul_add]

theorem kreinAdjoint_smul (c : ℂ) (A : M6C) :
    kreinAdjoint (c • A) = star c • kreinAdjoint A := by
  change kreinSymmetry * star (c • A) * kreinSymmetry =
    star c • kreinAdjoint A
  simp [star_smul, smul_mul_assoc, mul_smul_comm]
  rfl

lemma star_sheetTensor (P : SheetMatrix) (A : M3C) :
    star (sheetTensor P A) = sheetTensor (star P) (star A) := by
  ext s t
  simp [sheetTensor, Matrix.star_apply, mul_comm]

lemma kreinAdjoint_sheetTensor (P : SheetMatrix) (A : M3C) :
    kreinAdjoint (sheetTensor P A) =
      sheetTensor (sheetFlip * star P * sheetFlip) (star A) := by
  rw [kreinAdjoint, star_sheetTensor, kreinSymmetry]
  rw [sheetTensor_mul, sheetTensor_mul]
  simp [Matrix.mul_assoc]

lemma sheetFlip_conjugate_identity :
    sheetFlip * star sheetIdentity * sheetFlip = sheetIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetIdentity, Matrix.star_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

lemma sheetFlip_conjugate_parity :
    sheetFlip * star sheetParity * sheetFlip = -sheetParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetParity, Matrix.star_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

lemma sheetFlip_conjugate_flip :
    sheetFlip * star sheetFlip * sheetFlip = sheetFlip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two]

lemma sheetFlip_conjugate_phase :
    sheetFlip * star sheetPhase * sheetFlip = -sheetPhase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetPhase, Matrix.star_apply, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem kreinAdjoint_stokes (q : StokesQuad) :
    operatorStokesLinearEquiv
        (kreinAdjoint (assembleStokes q)) =
      stokesKreinAdjoint q := by
  rcases q with ⟨q₀, q₁, q₂, q₃⟩
  have hconj : kreinAdjoint (assembleStokes (q₀, q₁, q₂, q₃)) =
      assembleStokes (star q₀, star q₁, -star q₂, -star q₃) := by
    rw [assembleStokes_eq_pauli_expansion, assembleStokes_eq_pauli_expansion]
    simp only [pauliExpansion, kreinAdjoint_add, kreinAdjoint_sheetTensor,
      sheetFlip_conjugate_identity, sheetFlip_conjugate_parity,
      sheetFlip_conjugate_flip, sheetFlip_conjugate_phase]
    ext s t
    simp [sheetTensor]
    ring
  have hcoords (r : StokesQuad) : operatorStokesLinearEquiv (assembleStokes r) = r := by
    change blocksToStokes (blockLinearMap (blockLinearMapInv (stokesToBlocks r))) = r
    rw [blockLinearMap_blockLinearMapInv, blocksToStokes_stokesToBlocks]
  rw [hconj]
  exact hcoords (star q₀, star q₁, -star q₂, -star q₃)
end InfoGeometry.Canonical.TwoSheetKreinAdjoint
