/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CattoGurseySplitBasis
import InfoGeometry.Canonical.CattoGurseyBlockGrading
import Mathlib.Data.ZMod.Basic

/-!
# Corrected split-octonion identities and the separate 6|21 matrix algebra

The signed octonion basis, full coordinate transport, fusion, CAR-type
relations and generic parenthesized products are owned by
`Canonical.CattoGurseySplitBasis`; the basis associator and Jacobiator are
reused from `Canonical.GunaydinGurseyTripleProducts`, on the existing Zorn carrier. The sign
convention is `uZero=E22, uStarZero=E11, u_i=V_i, uStar_i=-U_i`.

The associative sector uses native `SuperMatrix 6 21 R`. Its homogeneous
superbracket and super-Jacobi identities come from `GLSupermatrixGradedLie`;
`CattoGurseyBlockGrading` identifies its blocks with the genuine Peirce direct
sum. Neither a special-unitary real form nor a multiplication-preserving
embedding of octonions into this matrix algebra is claimed. In fact the latter
is ruled out by `no_injective_associative_realization`.

The composite formula below retains both contributions to every block of
`Psi * Phi`. In particular `Psi * P * Phi` alone is not generally a diagonal
compression. The two inputs are arbitrary; no adjoint relation is smuggled in.
-/

namespace CattoGurseyOctonionicSuperalgebra

open InfoGeometry.Canonical.GLSupermatrixGradedLie

variable {R : Type*} [CommRing R]

/-- The actual 6|21 composite matrix, resolved into all four supported sectors. -/
theorem composite_sector_resolution (Psi Phi : SuperMatrix 6 21 R) :
    Psi * Phi =
      evenMatrix (blockA Psi * blockA Phi + blockB Psi * blockC Phi) 0 +
      evenMatrix 0 (blockC Psi * blockB Phi + blockD Psi * blockD Phi) +
      oddMatrix (blockA Psi * blockB Phi + blockB Psi * blockD Phi) 0 +
      oddMatrix 0 (blockC Psi * blockA Phi + blockD Psi * blockC Phi) := by
  have hp : Matrix.fromBlocks (blockA Psi) (blockB Psi) (blockC Psi) (blockD Psi) = Psi :=
    Matrix.fromBlocks_toBlocks Psi
  have hq : Matrix.fromBlocks (blockA Phi) (blockB Phi) (blockC Phi) (blockD Phi) = Phi :=
    Matrix.fromBlocks_toBlocks Phi
  calc
    Psi * Phi = Matrix.fromBlocks (blockA Psi) (blockB Psi) (blockC Psi) (blockD Psi) *
        Matrix.fromBlocks (blockA Phi) (blockB Phi) (blockC Phi) (blockD Phi) := by rw [hp,hq]
    _ = _ := by
      rw [Matrix.fromBlocks_multiply]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [evenMatrix, oddMatrix]

open InfoGeometry.Algebra
open InfoGeometry.Canonical.GunaydinGursey

/-- Nonvacuity and characteristic boundary on the same owned Zorn carrier:
the commutator Jacobiator vanishes in characteristic three, while the
associator does not. -/
theorem characteristic_three_boundary :
    ZornVectorMatrix.commutatorJacobiator (u 0 : ZornVectorMatrix (ZMod 3)) (u 1) (u 2) = 0 ∧
    ZornVectorMatrix.associator (u 0 : ZornVectorMatrix (ZMod 3)) (u 1) (u 2) ≠ 0 := by
  constructor
  · rw [triple_jacobiator, show (-6 : ZMod 3) = 0 by decide]
    exact ZornVectorMatrix.zero_smul _
  · rw [triple_associator]
    intro h
    have hh := congrArg ZornVectorMatrix.b h
    norm_num [ZornVectorMatrix.sub, ZornVectorMatrix.neg, uZero, uStarZero, ZornVectorMatrix.E11,
      ZornVectorMatrix.E22] at hh

/-- The advertised nonzero obstruction is realized over the integers. -/
theorem integer_jacobiator_nonzero :
    ZornVectorMatrix.commutatorJacobiator (u 0 : ZornVectorMatrix ℤ) (u 1) (u 2) ≠ 0 := by
  rw [jacobiator_ne_zero_iff]
  norm_num

/-- Regression for the invalid claim that `Psi * P * PsiBar` always lies in
`P A P`, even when `PsiBar` is the transpose of `Psi`. -/
theorem transported_support_need_not_be_original_corner :
    let p : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;0,0]
    let s : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;1,0]
    p * (s * p * s.transpose) * p ≠ s * p * s.transpose := by decide

end CattoGurseyOctonionicSuperalgebra
