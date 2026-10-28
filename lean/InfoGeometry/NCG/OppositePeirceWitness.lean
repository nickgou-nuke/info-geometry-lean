/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.OppositePeirceRealMetric
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Full real matrix witnesses for the Peirce coupling

A nondiagonal orthogonal support and nonsymmetric square-zero arrows give
noncommuting return channels. One coupling has a positive trace but a nonzero
kernel; another has a strictly positive square, certified by an explicit
inverse of the full coupling. No diagonalization is used in the proofs.
-/

noncomputable section

namespace InfoGeometry.NCG.OppositePeirceWitness

open Matrix
open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading
open InfoGeometry.NCG.OppositePeirceCoupling InfoGeometry.NCG.OppositePeirceTrace
open InfoGeometry.NCG.OppositePeirceRealMetric
open scoped Matrix

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

def support : Mat := !![1/2, 0, 1/2, 0; 0, 1/2, 0, 1/2;
  1/2, 0, 1/2, 0; 0, 1/2, 0, 1/2]

def singularArrow : Mat := !![3, -1, -3, 1; -(3/2), 1/2, 3/2, -(1/2);
  3, -1, -3, 1; -(3/2), 1/2, 3/2, -(1/2)]

def regularArrow : Mat := !![5/2, -(1/2), -(5/2), 1/2; -1, 0, 1, 0;
  5/2, -(1/2), -(5/2), 1/2; -1, 0, 1, 0]

def regularInverse : Mat := !![0, -(3/4), 0, 1/4; -(3/4), -(5/2), -(1/4), 0;
  0, -(1/4), 0, 3/4; 1/4, 0, 3/4, 5/2]

theorem support_idempotent : IsIdempotentElem support := by
  change support * support = support
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [support, Matrix.mul_apply, Fin.sum_univ_succ]

theorem support_selfadjoint : support.IsHermitian := by
  change supportᴴ = support
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [support, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

theorem singular_arrow_corner : component10 support singularArrow = singularArrow := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [component10, complementIdempotent, support, singularArrow, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem singular_arrow_nonzero : singularArrow ≠ 0 := by
  intro h
  have h0 := congrArg (fun M : Mat => M 0 0) h
  norm_num [singularArrow] at h0

theorem singular_arrow_square_zero : singularArrow * singularArrow = 0 := by
  have h := peirce10_mul_peirce10_eq_zero support support_idempotent.eq
    (component10_mem support singularArrow) (component10_mem support singularArrow)
  simpa only [singular_arrow_corner] using h

/-- Both directions are nonzero and they genuinely fail to commute. -/
theorem arrow_adjoint_noncommute :
    singularArrow * singularArrowᴴ ≠ singularArrowᴴ * singularArrow := by
  intro h
  have h0 := congrArg (fun M : Mat => M 0 0) h
  norm_num [singularArrow, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Fin.sum_univ_succ] at h0

theorem singular_coupling_formula :
    component10 support singularArrow + component01 support singularArrowᴴ =
      !![6, -(5/2), 0, -(1/2); -(5/2), 1, 1/2, 0;
        0, 1/2, -6, 5/2; -(1/2), 0, 5/2, -1] := by
  rw [component01_conjTranspose support_selfadjoint, singular_arrow_corner]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singularArrow, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

theorem singular_square_trace :
    Matrix.trace ((component10 support singularArrow + component01 support singularArrowᴴ) *
      (component10 support singularArrow + component01 support singularArrowᴴ)) = 100 := by
  rw [singular_coupling_formula]
  norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]

theorem singular_kernel_vector :
    (component10 support singularArrow + component01 support singularArrowᴴ) *ᵥ
      ![5, 12, 1, 0] = 0 := by
  rw [singular_coupling_formula]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Nonzero square and positive trace do not imply positive definiteness. -/
theorem singular_square_not_posDef :
    ¬((component10 support singularArrow + component01 support singularArrowᴴ) *
      (component10 support singularArrow + component01 support singularArrowᴴ)).PosDef := by
  intro h
  have hx : (![5, 12, 1, 0] : Fin 4 → ℝ) ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    norm_num at h0
  have hk : ((component10 support singularArrow + component01 support singularArrowᴴ) *
      (component10 support singularArrow + component01 support singularArrowᴴ)) *ᵥ
        ![5, 12, 1, 0] = 0 := by
    rw [← Matrix.mulVec_mulVec, singular_kernel_vector, Matrix.mulVec_zero]
  have hpos := h.dotProduct_mulVec_pos hx
  have : (0 : ℝ) < 0 := by simpa only [hk, dotProduct_zero] using hpos
  exact (lt_irrefl (0 : ℝ)) this

theorem regular_arrow_corner : component10 support regularArrow = regularArrow := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [component10, complementIdempotent, support, regularArrow, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem regular_coupling_formula :
    component10 support regularArrow + component01 support regularArrowᴴ =
      !![5, -(3/2), 0, -(1/2); -(3/2), 0, 1/2, 0;
        0, 1/2, -5, 3/2; -(1/2), 0, 3/2, 0] := by
  rw [component01_conjTranspose support_selfadjoint, regular_arrow_corner]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [regularArrow, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

theorem regular_left_inverse :
    regularInverse * (component10 support regularArrow + component01 support regularArrowᴴ) = 1 := by
  rw [regular_coupling_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [regularInverse, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- Strict positivity is achieved on a full, nonscalar, non-diagonal coupling. -/
theorem regular_square_posDef :
    ((component10 support regularArrow + component01 support regularArrowᴴ) *
      (component10 support regularArrow + component01 support regularArrowᴴ)).PosDef := by
  apply (square_posDef_iff support_idempotent support_selfadjoint regularArrow).mpr
  intro x hu hv
  rw [← component01_conjTranspose support_selfadjoint] at hv
  have hk := (sum_mulVec_zero_iff support_idempotent regularArrow regularArrowᴴ x).mpr ⟨hu, hv⟩
  calc
    x = (regularInverse * (component10 support regularArrow + component01 support regularArrowᴴ)) *ᵥ
        x := by rw [regular_left_inverse, Matrix.one_mulVec]
    _ = regularInverse *ᵥ
        ((component10 support regularArrow + component01 support regularArrowᴴ) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hk, Matrix.mulVec_zero]

end InfoGeometry.NCG.OppositePeirceWitness
