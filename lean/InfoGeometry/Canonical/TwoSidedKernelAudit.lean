/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceBilateralAction
import InfoGeometry.Analysis.BilateralGeneratorDerivative
import InfoGeometry.Algebra.ZornBilateralAction
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Exact noncommutative witnesses and interpretation boundaries. -/

namespace InfoGeometry.Canonical.TwoSidedKernelAudit

open Matrix InfoGeometry.Core.PeirceBilateralAction
open InfoGeometry.Core.DualSeedPeirce InfoGeometry.Core.PeirceRotor
open InfoGeometry.Core.DiracSuperalgebra

/-- Integral matrix units instantiate, rather than replace, the abstract carrier. -/
def dZ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
def bZ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

theorem integral_seed : IsDualSeedPair dZ bZ := by constructor <;> decide

/-- A noncommuting signal exhibits all four different corner multipliers. -/
theorem integral_four_corner_action :
    bilateral (diagonal dZ bZ (2 : ℤ) 3) (diagonal dZ bZ (5 : ℤ) 7)
      !![2, 3; 5, 7] = !![20, 42; 75, 147] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bilateral_apply, diagonal_formula, polePlus, poleMinus, exactSupport,
      coexactSupport, dZ, bZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Identity on diagonal corners and zero on both off-diagonal corners is not separable. -/
theorem four_weights_not_independent :
    ¬ ∃ l m r s : ℚ, l * r = 1 ∧ m * s = 1 ∧ l * s = 0 ∧ m * r = 0 := by
  rintro ⟨l, m, r, s, h1, h2, h3, h4⟩
  have h := weights_separable l m r s
  rw [h1, h2, h3, h4] at h
  norm_num at h

/-- At identity weights an active sandwich still discards the harmonic signal. -/
theorem proper_support_not_identity :
    let d : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
    let b : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 0; 1, 0, 0; 0, 0, 0]
    let x : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 0; 0, 0, 0; 0, 0, 1]
    bilateral (diagonal d b (1 : ℤ) 1) (diagonal d b (1 : ℤ) 1) x = 0 ∧ x ≠ 0 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [bilateral_apply, diagonal_formula, polePlus, poleMinus, exactSupport,
        coexactSupport, Matrix.mul_apply, Fin.sum_univ_three]
  · decide

/-- Symmetric sandwiching by an invertible diagonal need not preserve products. -/
theorem symmetric_sandwich_not_multiplicative :
    let d : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
    let b : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]
    let D := diagonal d b (2 : ℚ) (1 / 2)
    bilateral D D (d * b) ≠ bilateral D D d * bilateral D D b := by
  dsimp
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [bilateral_apply, diagonal_formula, polePlus, poleMinus, exactSupport,
    coexactSupport, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The source's extra reassociation is not the middle Moufang identity. -/
theorem invalid_reassociation :
    let k : InfoGeometry.Algebra.ZornVectorMatrix ℤ :=
      InfoGeometry.Algebra.ZornVectorMatrix.E11
    let x : InfoGeometry.Algebra.ZornVectorMatrix ℤ :=
      InfoGeometry.Algebra.ZornVectorMatrix.V 0
    let y : InfoGeometry.Algebra.ZornVectorMatrix ℤ :=
      InfoGeometry.Algebra.ZornVectorMatrix.V 1
    (k * x) * (y * k) ≠ k * (x * (y * k)) := by
  dsimp
  intro h
  have hu := congrArg (fun z : InfoGeometry.Algebra.ZornVectorMatrix ℤ => z.v 2) h
  norm_num [InfoGeometry.Algebra.zvm_mul_def,
    InfoGeometry.Algebra.ZornVectorMatrix.mul, InfoGeometry.Algebra.ZornVectorMatrix.E11,
    InfoGeometry.Algebra.ZornVectorMatrix.V, InfoGeometry.Algebra.ZornVec3.dot,
    InfoGeometry.Algebra.ZornVec3.cross, InfoGeometry.Algebra.ZornVec3.basis,
    Fin.sum_univ_three] at hu

#check bilateralEquiv
#check four_corner_expansion
#check symmetric_adjoint_selectivity
#check mixedUnit_inverse
#check diagonal_rotor_commutator
#check InfoGeometry.Analysis.BilateralGeneratorDerivative.hasDerivAt_bilateral
#check InfoGeometry.Analysis.BilateralGeneratorDerivative.hasDerivAt_commutator
#check InfoGeometry.Algebra.ZornBilateralAction.middle_moufang_operator
#check InfoGeometry.Algebra.ZornBilateralAction.distinct_kernels_do_not_commute

end InfoGeometry.Canonical.TwoSidedKernelAudit
