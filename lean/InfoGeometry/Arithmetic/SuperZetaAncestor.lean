import Mathlib.Analysis.Complex.Trigonometric
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Arithmetic.CenteredXiTwinKernel

/-!
# Finite chiral ancestor built from the native twin kernel

This file formalizes the finite matrix algebra that can honestly be built from
the existing `twinPlus`/`twinMinus` owner.  It does not identify the completed
Riemann zeta function with an odd Gaussian Mellin transform, and it does not
claim a Weil or Riemann-hypothesis theorem.

The diagonal parity matrix `chiralGamma` is kept distinct from the Weyl swap:
`chiralGamma` commutes with `a I + b chiralGamma`, whereas `chiralSwap` changes
the sign of the odd coefficient.  Thus the corrected finite Weyl statement is
implemented with `chiralSwap`.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.SuperZetaAncestor

open Matrix
open InfoGeometry.Arithmetic.CenteredXiTwinKernel

abbrev ChiralBlock (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- The diagonal `Z₂` parity matrix on the two chiral sheets. -/
def chiralGamma {R : Type*} [Ring R] : ChiralBlock R :=
  !![1, 0; 0, -1]

/-- The chiral Weyl swap, which exchanges the two diagonal sheets. -/
def chiralSwap {R : Type*} [Ring R] : ChiralBlock R :=
  !![0, 1; 1, 0]

/-- The finite operator `a I + b γ`, written in its diagonal chiral basis. -/
def superZetaOperator {R : Type*} [Ring R] (a b : R) : ChiralBlock R :=
  !![a + b, 0; 0, a - b]

@[simp] theorem chiralGamma_sq {R : Type*} [Ring R] :
    chiralGamma * chiralGamma = (1 : ChiralBlock R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGamma, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem chiralSwap_sq {R : Type*} [Ring R] :
    chiralSwap * chiralSwap = (1 : ChiralBlock R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralGamma_commutes_superZeta {R : Type*} [Ring R] (a b : R) :
    chiralGamma * superZetaOperator a b =
      superZetaOperator a b * chiralGamma := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGamma, superZetaOperator, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem chiralSwap_gamma_anticomm {R : Type*} [Ring R] :
    chiralSwap * chiralGamma + chiralGamma * chiralSwap =
      (0 : ChiralBlock R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralSwap, chiralGamma]

theorem chiralSwap_conjugates_superZeta {R : Type*} [Ring R] (a b : R) :
    chiralSwap * superZetaOperator a b * chiralSwap =
      superZetaOperator a (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralSwap, superZetaOperator, Matrix.mul_apply,
      Fin.sum_univ_two, sub_eq_add_neg]

theorem superZetaOperator_det {R : Type*} [CommRing R] (a b : R) :
    Matrix.det (superZetaOperator a b) = a ^ 2 - b ^ 2 := by
  simp [superZetaOperator, Matrix.det_fin_two]
  ring

/-- The unsymmetrized twin pair as a finite chiral diagonal operator. -/
def twinSuperZetaKernel (z : ℂ) (u : ℝ) : ChiralBlock ℂ :=
  superZetaOperator
    ((twinPlus z u + twinMinus z u) / 2)
    ((twinPlus z u - twinMinus z u) / 2)

theorem twinSuperZetaKernel_eq_diagonal (z : ℂ) (u : ℝ) :
    twinSuperZetaKernel z u =
      !![twinPlus z u, 0; 0, twinMinus z u] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twinSuperZetaKernel, superZetaOperator]
  <;> ring

theorem twinSuperZetaKernel_det (z : ℂ) (u : ℝ) :
    Matrix.det (twinSuperZetaKernel z u) =
      twinPlus z u * twinMinus z u := by
  rw [twinSuperZetaKernel_eq_diagonal]
  simp [Matrix.det_fin_two]

theorem twinSuperZetaKernel_imaginary_axis (E u : ℝ) :
    twinSuperZetaKernel ((E : ℂ) * Complex.I) u =
      !![(Real.cos (E * u) : ℂ) + (Real.sin (E * u) : ℂ) * Complex.I, 0;
         0, (Real.cos (E * u) : ℂ) - (Real.sin (E * u) : ℂ) * Complex.I] := by
  rw [twinSuperZetaKernel_eq_diagonal,
    twinPlus_imaginary_axis_eq_cos_add_sin,
    twinMinus_imaginary_axis_eq_cos_sub_sin]

theorem twinSuperZetaKernel_imaginary_axis_det (E u : ℝ) :
    Matrix.det (twinSuperZetaKernel ((E : ℂ) * Complex.I) u) = 1 := by
  rw [twinSuperZetaKernel_det]
  unfold twinPlus twinMinus
  rw [← Complex.exp_add]
  simp

/-- Conditional Weyl reflection for an even/odd coefficient pair.

The hypotheses are explicit because matrix conjugation alone does not prove
the functional equation of an analytic function. -/
theorem superZeta_weyl_conjugation
    (even odd : ℂ → ℂ) (s : ℂ)
    (heven : even (1 - s) = even s)
    (hodd : odd (1 - s) = -odd s) :
    superZetaOperator (even s) (odd s) =
      chiralSwap * superZetaOperator (even (1 - s)) (odd (1 - s)) * chiralSwap := by
  rw [chiralSwap_conjugates_superZeta, heven, hodd]
  simp

end InfoGeometry.Arithmetic.SuperZetaAncestor

end noncomputable section
