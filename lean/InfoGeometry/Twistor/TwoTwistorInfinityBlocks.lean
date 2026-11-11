/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwoTwistorGramMass
import InfoGeometry.Twistor.ConstituentColumnEquivalence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Infinity-form blocks and the square-zero raised matrix

The covariant alternating form, its curried dual map, and its raised matrix
are kept distinct. In particular the alternating lower block squares to
minus the lower projector, whereas its Witt-raised matrix squares to zero.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwoTwistorInfinityBlocks

open PenroseIncidence PerjesConventions TwistorKinematicTensor
open TwistorConstituentKinematics InfinityTwistor ConstituentColumnEquivalence
open TwoTwistorGramMass
open scoped Matrix

/-- Rank two of the native dual-valued form, from its already-proved radical. -/
theorem finrank_range_infinityTwistor :
    Module.finrank ℂ (LinearMap.range infinityTwistor) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker infinityTwistor
  have hs := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.snd ℂ Spinor2 Spinor2)
  rw [ker_infinityTwistor] at h
  calc
    Module.finrank ℂ (LinearMap.range infinityTwistor) =
        Module.finrank ℂ (LinearMap.range (LinearMap.snd ℂ Spinor2 Spinor2)) :=
      Nat.add_right_cancel (h.trans hs.symm)
    _ = 2 := by
      have hr : LinearMap.range (LinearMap.snd ℂ Spinor2 Spinor2) = ⊤ :=
        LinearMap.range_eq_top.mpr LinearMap.snd_surjective
      rw [hr, finrank_top]
      exact Module.finrank_fin_fun

def epsilon : ComplexSpacetime := !![0, 1; -1, 0]

/-- Lower-spinor columns in the same constituent order as `gram`. -/
def lowerFrame (Z : PairFrame) : ComplexSpacetime := fun a i => (Z i).2 a

def upperFrame (Z : PairFrame) : ComplexSpacetime := fun a i => (Z i).1 a

theorem gram_eq_block_products (Z : PairFrame) :
    gram Z = (upperFrame Z)ᴴ * lowerFrame Z + (lowerFrame Z)ᴴ * upperFrame Z := by
  ext i j
  simp [gram, wittPair, upperFrame, lowerFrame, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem lowerFrame_det (Z : PairFrame) :
    (lowerFrame Z).det = infinityTwistor (Z 0) (Z 1) := by
  simp [lowerFrame, Matrix.det_fin_two, infinityTwistor]
  ring

/-- Pullback of the lower alternating form by a general, not necessarily invertible frame. -/
theorem lowerFrame_epsilon (Z : PairFrame) :
    (lowerFrame Z)ᵀ * epsilon * lowerFrame Z = (lowerFrame Z).det • epsilon := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [epsilon, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem lowerFrame_epsilon_pairing (Z : PairFrame) (i j : Fin 2) :
    ((lowerFrame Z)ᵀ * epsilon * lowerFrame Z) i j = infinityTwistor (Z i) (Z j) := by
  simp [epsilon, lowerFrame, Matrix.mul_apply, Fin.sum_univ_two, infinityTwistor]
  ring

/-- The conjugate-first momentum convention, retaining the full matrix product. -/
theorem momentum_eq_block_product (Z : PairFrame) :
    momentum (Z 0) + momentum (Z 1) = (lowerFrame Z).map star * (lowerFrame Z)ᵀ := by
  ext a b
  simp [momentum, lowerFrame, Matrix.vecMulVec, Matrix.mul_apply, Fin.sum_univ_two]

/-- Coordinate matrix of the covariant infinity alternating form. -/
def infinityLower : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

def wittMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

def lowerProjector : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem infinityLower_transpose : infinityLowerᵀ = -infinityLower := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [infinityLower]

theorem infinityLower_square : infinityLower * infinityLower = -lowerProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [infinityLower, lowerProjector, Matrix.mul_apply, Fin.sum_univ_four]

theorem infinityLower_not_idempotent : infinityLower * infinityLower ≠ infinityLower := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 2 2) h
  rw [infinityLower_square] at he
  norm_num [infinityLower, lowerProjector] at he

theorem infinityLower_square_ne_zero : infinityLower * infinityLower ≠ 0 := by
  rw [infinityLower_square]
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 2 2) h
  norm_num [lowerProjector] at he

/-- Raising with the Witt matrix gives the existing infinity-raising operator. -/
theorem witt_raise_infinityLower :
    wittMatrix * infinityLower = infinityRaisingMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wittMatrix, infinityLower, infinityRaisingMatrix,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem raised_infinity_square_zero :
    (wittMatrix * infinityLower) * (wittMatrix * infinityLower) = 0 := by
  rw [witt_raise_infinityLower]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [infinityRaisingMatrix, Matrix.mul_apply, Fin.sum_univ_four]

/-- Raising on opposite sides gives different operators. -/
theorem witt_infinity_noncommuting :
    wittMatrix * infinityLower ≠ infinityLower * wittMatrix := by
  intro h
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 3) h
  norm_num [wittMatrix, infinityLower, Matrix.mul_apply, Fin.sum_univ_four] at h03

/-- This formula fixes the covariant sign by evaluating both actual columns. -/
theorem infinityLower_column_pairing (Z : PairFrame) :
    (columnEquiv Z)ᵀ * infinityLower * columnEquiv Z =
      (lowerFrame Z).det • epsilon := by
  rw [← lowerFrame_epsilon]
  have hcol (a : Fin 4) (i : Fin 2) :
      columnEquiv Z a i = ![(Z i).1 0, (Z i).1 1, (Z i).2 0, (Z i).2 1] a := rfl
  ext i j
  simp [hcol, infinityLower, lowerFrame, epsilon, Matrix.transpose_apply,
    Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

/-- Full covariant-infinity contraction of the actual alternating column tensor. -/
def infinityContraction (Z : PairFrame) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, infinityLower a b *
    (columnEquiv Z a 0 * columnEquiv Z b 1 - columnEquiv Z a 1 * columnEquiv Z b 0)

theorem infinityContraction_eq_twice_pairing (Z : PairFrame) :
    infinityContraction Z = 2 * infinityTwistor (Z 0) (Z 1) := by
  have hcol (a : Fin 4) (i : Fin 2) :
      columnEquiv Z a i = ![(Z i).1 0, (Z i).1 1, (Z i).2 0, (Z i).2 1] a := rfl
  simp [infinityContraction, infinityLower, hcol, infinityTwistor,
    Fin.sum_univ_four]
  ring

theorem paperMassSq_eq_half_infinityContraction (Z : PairFrame) :
    paperMassSq Z = Complex.normSq (infinityContraction Z) / 2 := by
  rw [paperMassSq_eq_infinity_normSq, infinityContraction_eq_twice_pairing,
    Complex.normSq_mul]
  norm_num [Complex.normSq_apply]
  ring

end InfoGeometry.Twistor.TwoTwistorInfinityBlocks
