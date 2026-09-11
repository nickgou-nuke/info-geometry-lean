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

theorem kreinAdjoint_stokes (q : StokesQuad) :
    operatorStokesLinearEquiv
        (kreinAdjoint (assembleStokes q)) =
      stokesKreinAdjoint q := by
  apply stokesLinearEquiv.symm.injective
  simp only [operatorStokesLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  change blockLinearEquiv (kreinAdjoint (assembleStokes q)) =
    stokesToBlocks (stokesKreinAdjoint q)
  rcases q with ⟨a0, a1, a2, a3⟩
  apply Prod.ext
  · ext i j
    simp [assembleStokes, stokesKreinAdjoint, kreinAdjoint,
      kreinSymmetry, sheetTensor, sheetFlip, stokesToBlocks,
      blocksToStokes, blockLinearEquiv_apply, blockLinearEquiv,
      blockLinearMap, blockLinearMapInv, Matrix.star_apply,
      Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.sub_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_succ] <;> ring
  · apply Prod.ext
    · ext i j
      simp [assembleStokes, stokesKreinAdjoint, kreinAdjoint,
        kreinSymmetry, sheetTensor, sheetFlip, stokesToBlocks,
        blocksToStokes, blockLinearEquiv_apply, blockLinearEquiv,
        blockLinearMap, blockLinearMapInv, Matrix.star_apply,
        Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.sub_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_succ] <;> ring
    · apply Prod.ext
      · ext i j
        simp [assembleStokes, stokesKreinAdjoint, kreinAdjoint,
          kreinSymmetry, sheetTensor, sheetFlip, stokesToBlocks,
          blocksToStokes, blockLinearEquiv_apply, blockLinearEquiv,
          blockLinearMap, blockLinearMapInv, Matrix.star_apply,
          Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.sub_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_succ] <;> ring
      · ext i j
        simp [assembleStokes, stokesKreinAdjoint, kreinAdjoint,
          kreinSymmetry, sheetTensor, sheetFlip, stokesToBlocks,
          blocksToStokes, blockLinearEquiv_apply, blockLinearEquiv,
          blockLinearMap, blockLinearMapInv, Matrix.star_apply,
          Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.sub_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_succ] <;> ring

end InfoGeometry.Canonical.TwoSheetKreinAdjoint
