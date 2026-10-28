/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! # Jacobi differentiation on full complex matrices

The real parameter is allowed to move in every complex matrix direction.
No self-adjointness or commutation assumption enters the determinant rule.
-/

noncomputable section

namespace InfoGeometry.Analysis.ComplexMatrixJacobi

open scoped Matrix Matrix.Norms.L2Operator Polynomial ContDiff
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The full Leibniz differential of the complex determinant. -/
def detLeibnizDerivative (A B : Mat) : ℂ :=
  ∑ σ : Equiv.Perm n,
    (Equiv.Perm.sign σ : ℂ) *
      ∑ i : n, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i

theorem hasDerivAt_det_leibniz
    {X : ℝ → Mat} {X' : Mat} {t : ℝ}
    (hX : ∀ i j : n, HasDerivAt (fun z : ℝ => X z i j) (X' i j) t) :
    HasDerivAt (fun z : ℝ => (X z).det)
      (detLeibnizDerivative (X t) X') t := by
  have hsum :
      HasDerivAt
        (fun z : ℝ => ∑ σ : Equiv.Perm n,
          (Equiv.Perm.sign σ : ℂ) * ∏ i : n, X z (σ i) i)
        (detLeibnizDerivative (X t) X') t := by
    apply HasDerivAt.fun_sum
    intro σ _
    have hp := HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun i z => X z (σ i) i) (f' := fun i => X' (σ i) i)
      (x := t) (fun i _ => hX (σ i) i)
    simpa [detLeibnizDerivative, Finset.mul_sum, smul_eq_mul] using
      hp.const_mul (Equiv.Perm.sign σ : ℂ)
  simpa [detLeibnizDerivative, Matrix.det_apply'] using hsum

theorem hasDerivAt_det_one_add_smul_zero (M : Mat) :
    HasDerivAt (fun t : ℝ => (1 + t • M).det) (Matrix.trace M) 0 := by
  let p : ℂ[X] := Matrix.det (1 + (Polynomial.X : ℂ[X]) • M.map Polynomial.C)
  have hpder : p.derivative.eval 0 = Matrix.trace M := by
    simpa [p] using Matrix.derivative_det_one_add_X_smul (R := ℂ) M
  have hp := Polynomial.hasDerivAt (p := p) (x := (0 : ℂ))
  rw [hpder] at hp
  have hp' := hp.comp_ofReal
  convert hp' using 1
  ext t
  simp [p, eval_det, ← Matrix.smul_eq_mul_diagonal]

theorem detLeibnizDerivative_eq_det_mul_trace_inv_mul
    (A B : Mat) (hA : IsUnit A.det) :
    detLeibnizDerivative A B = A.det * Matrix.trace (A⁻¹ * B) := by
  let C : Mat := A⁻¹ * B
  have hfactor (t : ℝ) : A + t • B = A * (1 + t • C) := by
    dsimp [C]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv A hA, Matrix.one_mul]
  have hraw : HasDerivAt (fun t : ℝ => (A + t • B).det)
      (detLeibnizDerivative A B) 0 := by
    have h := hasDerivAt_det_leibniz (X := fun t : ℝ => A + t • B)
      (X' := B) (t := 0) (by
        intro i j
        simpa [Matrix.smul_apply, smul_eq_mul] using
          ((hasDerivAt_id' (0 : ℝ)).smul_const (B i j)).const_add (A i j))
    simpa using h
  have hprod := (hasDerivAt_det_one_add_smul_zero C).const_mul A.det
  have heq : (fun t : ℝ => (A + t • B).det) =
      (fun t : ℝ => A.det * (1 + t • C).det) := by
    funext t
    rw [hfactor, Matrix.det_mul]
  rw [heq] at hraw
  exact hraw.unique hprod

theorem hasDerivAt_det
    {X : ℝ → Mat} {X' : Mat} {t : ℝ}
    (hX : ∀ i j : n, HasDerivAt (fun z : ℝ => X z i j) (X' i j) t)
    (hunit : IsUnit (X t)) :
    HasDerivAt (fun z : ℝ => (X z).det)
      ((X t).det * Matrix.trace ((X t)⁻¹ * X')) t := by
  rw [← detLeibnizDerivative_eq_det_mul_trace_inv_mul _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)]
  exact hasDerivAt_det_leibniz hX

theorem differentiable_det : Differentiable ℝ (Matrix.det : Mat → ℂ) := by
  classical
  have heval (i j : n) : Differentiable ℝ (fun A : Mat => A i j) :=
    (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.differentiable
  change Differentiable ℝ (fun A : Mat => A.det)
  simp_rw [Matrix.det_apply']
  fun_prop

/-- The determinant is smooth to every native mathlib differentiability order. -/
theorem contDiff_det (k : ℕ∞ω) : ContDiff ℝ k (Matrix.det : Mat → ℂ) := by
  classical
  have heval (i j : n) : ContDiff ℝ k (fun A : Mat => A i j) :=
    (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.contDiff
  change ContDiff ℝ k (fun A : Mat => A.det)
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  exact contDiff_const.mul (contDiff_prod (fun i _ => heval (σ i) i))

end InfoGeometry.Analysis.ComplexMatrixJacobi
