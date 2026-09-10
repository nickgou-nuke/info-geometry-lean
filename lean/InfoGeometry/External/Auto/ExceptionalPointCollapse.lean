import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exceptional-point dimensional collapse

Finite Jones-matrix proof of the Drazin/exceptional-point shear collapse.
For the nontrivial unipotent shear `N(x) = [[1,x],[0,1]]`, every eigenvector
with eigenvalue `1` has zero second component.  Thus the eigenspace is the
single Jones line spanned by `[1,0]^T` when `x ≠ 0`.

This is the algebraic core of the "polarization black-hole" / EP defect story.
It proves a finite matrix fact, not a fabrication-certified physical device.
-/

noncomputable section

open Matrix Complex

namespace InfoGeometry.GrandUnification.ExceptionalPointCollapse

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev C2 := Matrix (Fin 2) (Fin 1) ℂ

/-- Nontrivial unipotent KAN shear / Drazin defect. -/
def shearN (x : ℂ) : M2C := !![1, x; 0, 1]

/-- First Jones basis vector. -/
def e0 : C2 := !![1; 0]

/-- Second Jones basis vector. -/
def e1 : C2 := !![0; 1]

/-- Eigenvector predicate for finite Jones vectors. -/
def IsEigenvector (A : M2C) (lam : ℂ) (v : C2) : Prop :=
  A * v = lam • v

/-- The nontrivial shear has characteristic polynomial `(λ-1)^2`, encoded by trace/det. -/
theorem shearN_trace_det (x : ℂ) :
    Matrix.trace (shearN x) = 2 ∧ (shearN x).det = 1 := by
  constructor
  · simp [shearN, Matrix.trace]
    norm_num
  · simp [shearN, Matrix.det_fin_two]

/-- The unipotent shear is genuinely nonzero away from `x=0`. -/
theorem shearN_ne_identity_of_ne_zero {x : ℂ} (hx : x ≠ 0) :
    shearN x ≠ (1 : M2C) := by
  intro h
  have hx0 : x = 0 := by
    have hentry := congr_fun (congr_fun h (0 : Fin 2)) (1 : Fin 2)
    simpa [shearN] using hentry
  simp [hx0] at hx

/-- The surviving Jones line is an eigenline. -/
theorem shearN_e0_eigen (x : ℂ) : IsEigenvector (shearN x) 1 e0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearN, e0]

/-- The transverse Jones axis is not an eigenvector when the shear is nontrivial. -/
theorem shearN_e1_not_eigen {x : ℂ} (hx : x ≠ 0) :
    ¬ IsEigenvector (shearN x) 1 e1 := by
  intro h
  have hentry := congr_fun (congr_fun h (0 : Fin 2)) (0 : Fin 1)
  have hx0 : x = 0 := by
    simpa [IsEigenvector, shearN, e1] using hentry
  simp [hx0] at hx

/-- Exceptional-point dimensional collapse: every `λ=1` eigenvector has zero second component. -/
theorem ep_dimensional_collapse {x : ℂ} {v : C2}
    (hx : x ≠ 0) (heig : IsEigenvector (shearN x) 1 v) :
    v 1 0 = 0 := by
  have hentry : (shearN x * v) 0 0 = ((1 : ℂ) • v) 0 0 := by
    exact congr_fun (congr_fun heig (0 : Fin 2)) (0 : Fin 1)
  have hraw : (∑ k : Fin 2, shearN x 0 k * v k 0) = v 0 0 := by
    simpa [Matrix.mul_apply] using hentry
  have hmul : x * v 1 0 = 0 := by
    simpa [shearN, Fin.sum_univ_two] using hraw
  exact mul_eq_zero.mp hmul |>.resolve_left hx

/-- Equivalently, every eigenvector is a scalar multiple of the surviving line. -/
theorem ep_eigenvector_on_surviving_line {x : ℂ} {v : C2}
    (hx : x ≠ 0) (heig : IsEigenvector (shearN x) 1 v) :
    v = (v 0 0) • e0 := by
  have hy := ep_dimensional_collapse hx heig
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e0, hy]

end InfoGeometry.GrandUnification.ExceptionalPointCollapse
