/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixProductState
import InfoGeometry.Canonical.BitWordComplexStageReindex
import InfoGeometry.Categorical.FiniteWordPathWeights

/-! Word-indexed evaluations of the product functional on the matrix colimit.
The native coherent index equivalence is used; no Cuntz quotient identification
or KMS property is assumed.
-/
noncomputable section
namespace InfoGeometry.QuantumContext.MatrixStageProductDensity

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Canonical.BitWordComplexStageReindex
open InfoGeometry.Categorical.FiniteWordPathWeights

/-- The recursive density is the unnormalized product of its letter weights. -/
theorem diagonalWeight_bitWord (q : Fin 2 → ℝ) (n : ℕ) (w : BitWord n) :
    diagonalWeight q n (bitWordFinPowTwoEquiv n w) =
      (2 : ℝ) ^ n * wordWeight q (fun i => finTwoEquivBool.symm (w i)) := by
  unfold wordWeight
  induction n with
  | zero => simp [diagonalWeight]
  | succ n ih =>
      obtain ⟨⟨u, b⟩, rfl⟩ := (bitWordSuccEquiv n).surjective w
      rw [finPowTwoEquiv_succ_apply]
      simp only [diagonalWeight, Equiv.symm_apply_apply]
      rw [ih, Fin.prod_univ_castSucc]
      simp [bitWordSuccEquiv, extendSucc, pow_succ]
      ring

/-- Word matrix units have product weights on the diagonal and zero elsewhere. -/
theorem productFunctional_wordMatrixUnit (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (n : ℕ) (u v : BitWord n) :
    productFunctional q hq (stageInjection n
      (Matrix.single (bitWordFinPowTwoEquiv n u) (bitWordFinPowTwoEquiv n v) (1 : ℂ))) =
      if u = v then ((wordWeight q (fun i => finTwoEquivBool.symm (u i)) : ℝ) : ℂ) else 0 := by
  rw [productFunctional_matrixUnit]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs with h
  · rw [diagonalWeight_bitWord]
    push_cast
    field_simp
  · rfl

end InfoGeometry.QuantumContext.MatrixStageProductDensity
end
