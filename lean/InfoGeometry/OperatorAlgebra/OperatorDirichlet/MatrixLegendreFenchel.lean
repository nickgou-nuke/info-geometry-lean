/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixLegendre
import InfoGeometry.Convex.FenchelConjugate
import InfoGeometry.Convex.Bregman
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Matrix quadratic conjugates and the existing Bregman expression

The matrix owner already proves completion of the square and an attained
greatest value. This file connects that value to the existing real-valued
`Convex.fenchelConj`, using the native continuous dot-product covector. It then
identifies the same gap with the existing algebraic-covector Bregman expression.
The matrix may be fully non-diagonal. Positive definiteness is explicit; no
supplied dual potential is assumed to be a convex conjugate.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The attained matrix-quadratic maximum computes the existing Fenchel
conjugate at every finite dot-product covector. -/
theorem fenchelConj_quadForm {A : Matrix n n ℝ} (hA : A.PosDef) (y : n → ℝ) :
    InfoGeometry.Convex.fenchelConj (fun x => (1 / 2 : ℝ) * quadForm A x)
        ((dotProductBilin ℝ ℝ y).toContinuousLinearMap) =
      (1 / 2 : ℝ) * quadForm A⁻¹ y := by
  let f : (n → ℝ) → ℝ := fun x => (1 / 2 : ℝ) * quadForm A x
  let ξ : (n → ℝ) →L[ℝ] ℝ := (dotProductBilin ℝ ℝ y).toContinuousLinearMap
  have hset : InfoGeometry.Convex.fenchelSet f ξ =
      Set.range (fun x : n → ℝ => x ⬝ᵥ y - (1 / 2 : ℝ) * quadForm A x) := by
    change Set.range (fun x : n → ℝ => y ⬝ᵥ x - (1 / 2 : ℝ) * quadForm A x) = _
    congr 1
    funext x
    rw [dotProduct_comm]
  have hvalue : InfoGeometry.Convex.dualPair ξ (A⁻¹ *ᵥ y) - f (A⁻¹ *ᵥ y) =
      (1 / 2 : ℝ) * quadForm A⁻¹ y := by
    change y ⬝ᵥ (A⁻¹ *ᵥ y) - (1 / 2 : ℝ) * quadForm A (A⁻¹ *ᵥ y) = _
    rw [dotProduct_comm]
    exact fenchel_young_eq hA y
  have hgreatest : IsGreatest (InfoGeometry.Convex.fenchelSet f ξ)
      (InfoGeometry.Convex.dualPair ξ (A⁻¹ *ᵥ y) - f (A⁻¹ *ᵥ y)) := by
    rw [hset, hvalue]
    exact legendre_conjugate_isGreatest hA y
  exact (InfoGeometry.Convex.fenchelConj_eq_of_isGreatest f ξ (A⁻¹ *ᵥ y)
    hgreatest).trans hvalue

/-- The actual Fenchel gap is the weighted square of the primal residual. -/
theorem fenchelConj_quadForm_gap {A : Matrix n n ℝ} (hA : A.PosDef)
    (x y : n → ℝ) :
    (1 / 2 : ℝ) * quadForm A x +
        InfoGeometry.Convex.fenchelConj (fun z => (1 / 2 : ℝ) * quadForm A z)
          ((dotProductBilin ℝ ℝ y).toContinuousLinearMap) - x ⬝ᵥ y =
      (1 / 2 : ℝ) * quadForm A (x - A⁻¹ *ᵥ y) := by
  rw [fenchelConj_quadForm hA y]
  have h := legendre_complete_square (posDef_transpose_eq hA)
    (posDef_det_isUnit hA) x y
  apply (sub_eq_iff_eq_add).2
  simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp h).symm

/-- The same actual gap is the inverse-metric square of the dual residual,
with the attachment's sign and factor. -/
theorem fenchelConj_quadForm_gap_dual_residual {A : Matrix n n ℝ} (hA : A.PosDef)
    (x y : n → ℝ) :
    (1 / 2 : ℝ) * quadForm A x +
        InfoGeometry.Convex.fenchelConj (fun z => (1 / 2 : ℝ) * quadForm A z)
          ((dotProductBilin ℝ ℝ y).toContinuousLinearMap) - x ⬝ᵥ y =
      (1 / 2 : ℝ) * quadForm A⁻¹ (A *ᵥ x - y) := by
  let z := x - A⁻¹ *ᵥ y
  have hAz : A *ᵥ z = A *ᵥ x - y := by
    dsimp [z]
    rw [mulVec_sub, mulVec_inv_mulVec (posDef_det_isUnit hA)]
  have hinv : A⁻¹ *ᵥ (A *ᵥ z) = z := by
    rw [mulVec_mulVec, (hessian_product hA).2.1, one_mulVec]
  have hquad : quadForm A⁻¹ (A *ᵥ z) = quadForm A z := by
    simp only [quadForm, hinv]
    exact dotProduct_comm _ _
  rw [fenchelConj_quadForm_gap hA x y, ← hAz, hquad]

/-- Positive definiteness identifies the zero set of the actual Fenchel gap
with the linear Legendre relation. -/
theorem fenchelConj_quadForm_gap_eq_zero_iff {A : Matrix n n ℝ} (hA : A.PosDef)
    (x y : n → ℝ) :
    (1 / 2 : ℝ) * quadForm A x +
        InfoGeometry.Convex.fenchelConj (fun z => (1 / 2 : ℝ) * quadForm A z)
          ((dotProductBilin ℝ ℝ y).toContinuousLinearMap) - x ⬝ᵥ y = 0 ↔
      y = A *ᵥ x := by
  rw [fenchelConj_quadForm_gap hA x y]
  constructor
  · intro h
    have hz : x - A⁻¹ *ᵥ y = 0 := by
      by_contra hz
      have hp : 0 < quadForm A (x - A⁻¹ *ᵥ y) := by
        simpa [quadForm] using hA.dotProduct_mulVec_pos hz
      linarith
    have hx := sub_eq_zero.mp hz
    calc
      y = A *ᵥ (A⁻¹ *ᵥ y) := (mulVec_inv_mulVec (posDef_det_isUnit hA) y).symm
      _ = A *ᵥ x := by rw [← hx]
  · intro hy
    have hinv : A⁻¹ *ᵥ (A *ᵥ x) = x := by
      rw [mulVec_mulVec, (hessian_product hA).2.1, one_mulVec]
    rw [hy, hinv, sub_self]
    simp [quadForm]

/-- The repository's Bregman expression for the symmetric metric covector
is exactly the weighted displacement square. Positivity is not needed here. -/
theorem bregmanDivergence_quadForm (A : Matrix n n ℝ) (hA : Aᵀ = A)
    (x y : n → ℝ) :
    InfoGeometry.bregmanDivergence (fun z => (1 / 2 : ℝ) * quadForm A z)
        (fun z => A.toBilin' z) x y =
      (1 / 2 : ℝ) * quadForm A (x - y) := by
  have hsym : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  simp only [InfoGeometry.bregmanDivergence, InfoGeometry.pairing,
    Matrix.toBilin'_apply', quadForm, mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [hsym]
  ring

/-- The actual Fenchel gap is the existing Bregman expression based at the
inverse Legendre point, so the two owner APIs describe the same quantity. -/
theorem fenchelConj_quadForm_gap_eq_bregmanDivergence {A : Matrix n n ℝ}
    (hA : A.PosDef) (x y : n → ℝ) :
    (1 / 2 : ℝ) * quadForm A x +
        InfoGeometry.Convex.fenchelConj (fun z => (1 / 2 : ℝ) * quadForm A z)
          ((dotProductBilin ℝ ℝ y).toContinuousLinearMap) - x ⬝ᵥ y =
      InfoGeometry.bregmanDivergence (fun z => (1 / 2 : ℝ) * quadForm A z)
        (fun z => A.toBilin' z) x (A⁻¹ *ᵥ y) := by
  rw [fenchelConj_quadForm_gap hA x y,
    bregmanDivergence_quadForm A (posDef_transpose_eq hA)]

end InfoGeometry.OperatorAlgebra.OperatorDirichlet
