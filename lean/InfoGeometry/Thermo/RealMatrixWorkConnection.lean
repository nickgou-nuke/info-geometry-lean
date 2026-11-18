/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.RealMatrixGibbs
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Additive work transport on full real matrix controls

The base consists of pairs `(ρ, H)` of arbitrary real square matrices. The
one-form `α_(ρ,H)(R,A) = Tr(ρ * A)` is built from native continuous bilinear
matrix multiplication and the continuous trace. Its actual Fréchet derivative
gives `dα(v,w) = Tr(v.1 * w.2 - w.1 * v.2)` in the displayed product order.

The extra real coordinate records work done on the system. The connection on
the trivial additive real bundle is `Θ = dw - α`; its curvature is therefore
`-dα`. The interval integral constructs horizontal lifts and affine transport.
This is additive thermodynamic work holonomy, not a purification connection or
an operator-valued phase. No commutation of matrix arguments is assumed.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealMatrixWorkConnection

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Interval

/-! ## Transport of the real work coordinate -/

/-- Translation by the actual integrated work-on current. -/
def workOnTransport (current : ℝ → ℝ) (a b : ℝ) : ℝ ≃ᵃ[ℝ] ℝ :=
  AffineEquiv.constVAdd ℝ ℝ (∫ t in a..b, current t)

@[simp] theorem workOnTransport_apply (current : ℝ → ℝ) (a b w : ℝ) :
    workOnTransport current a b w = w + ∫ t in a..b, current t := by
  change (∫ t in a..b, current t) + w = w + ∫ t in a..b, current t
  exact add_comm _ _

@[simp] theorem workOnTransport_same (current : ℝ → ℝ) (a : ℝ) :
    workOnTransport current a a = AffineEquiv.refl ℝ ℝ := by
  simp [workOnTransport]

/-- Reversing the interval gives the inverse affine translation. -/
theorem workOnTransport_symm (current : ℝ → ℝ) (a b : ℝ) :
    (workOnTransport current a b).symm = workOnTransport current b a := by
  unfold workOnTransport
  rw [AffineEquiv.constVAdd_symm, intervalIntegral.integral_symm a b]

/-- Transport composes by the native adjacent-interval integral theorem. -/
theorem workOnTransport_trans (current : ℝ → ℝ) (a b c : ℝ)
    (hab : IntervalIntegrable current volume a b)
    (hbc : IntervalIntegrable current volume b c) :
    (workOnTransport current a b).trans (workOnTransport current b c) =
      workOnTransport current a c := by
  ext w
  simp only [AffineEquiv.trans_apply, workOnTransport_apply]
  rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals hab hbc]

/-- The work coordinate of the lift with prescribed initial value. -/
def workOnLift (current : ℝ → ℝ) (a w : ℝ) (t : ℝ) : ℝ :=
  w + ∫ s in a..t, current s

@[simp] theorem workOnLift_initial (current : ℝ → ℝ) (a w : ℝ) :
    workOnLift current a w a = w := by
  simp [workOnLift]

theorem workOnLift_eq_transport (current : ℝ → ℝ) (a w t : ℝ) :
    workOnLift current a w t = workOnTransport current a t w := by
  rw [workOnTransport_apply]
  rfl

/-- Native interval FTC proves the horizontal work equation. -/
theorem hasDerivAt_workOnLift (current : ℝ → ℝ) (hcurrent : Continuous current)
    (a w t : ℝ) :
    HasDerivAt (workOnLift current a w) (current t) t := by
  exact (hcurrent.integral_hasStrictDerivAt a t).hasDerivAt.const_add w

/-! ## The full matrix work form and its differential -/

/-- Matrix density and Hamiltonian controls, with no diagonal reduction. -/
abbrev Base (n : Type*) := Matrix n n ℝ × Matrix n n ℝ

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℝ

/-- Ordered multiplication followed by the existing native continuous trace. -/
def traceMul : Mat →L[ℝ] Mat →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Mat Mat ℝ) RealMatrixGibbs.traceCLM).comp
    (ContinuousLinearMap.mul ℝ Mat)

@[simp] theorem traceMul_apply (R A : Mat) :
    traceMul R A = Matrix.trace (R * A) := rfl

/-- The work one-form `α_(ρ,H)(R,A) = Tr(ρ * A)`, continuously linear in its
tangent argument and continuously linear in the ambient base coordinates. -/
def workForm : Base n →L[ℝ] Base n →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Base n) Mat ℝ).flip
      (ContinuousLinearMap.snd ℝ Mat Mat)).comp
    (traceMul.comp (ContinuousLinearMap.fst ℝ Mat Mat))

@[simp] theorem workForm_apply (x v : Base n) :
    workForm x v = Matrix.trace (x.1 * v.2) := rfl

/-- The derivative is obtained from the constructed native continuous linear
map into the space of continuous linear one-forms. -/
theorem hasFDerivAt_workForm (x : Base n) :
    HasFDerivAt (workForm (n := n)) workForm x :=
  workForm.hasFDerivAt

/-- The alternating differential `dα`. The curvature of `dw - α` has the
opposite sign. -/
def workCurvature : Base n →L[ℝ] Base n →L[ℝ] ℝ :=
  workForm - (workForm (n := n)).flip

/-- Curvature is the alternation of the actual Fréchet derivative. -/
theorem workCurvature_eq_alternating_fderiv (x v w : Base n) :
    workCurvature v w =
      fderiv ℝ (workForm (n := n)) x v w -
        fderiv ℝ (workForm (n := n)) x w v := by
  rw [(hasFDerivAt_workForm x).fderiv]
  rfl

theorem workCurvature_apply (v w : Base n) :
    workCurvature v w = Matrix.trace (v.1 * w.2 - w.1 * v.2) := by
  change Matrix.trace (v.1 * w.2) - Matrix.trace (w.1 * v.2) = _
  exact (Matrix.trace_sub _ _).symm

@[simp] theorem workCurvature_self (v : Base n) : workCurvature v v = 0 := by
  simp [workCurvature]

theorem workCurvature_skew (v w : Base n) :
    workCurvature v w = -workCurvature w v := by
  change workForm v w - workForm w v = -(workForm w v - workForm v w)
  exact (neg_sub (workForm w v) (workForm v w)).symm

/-! ## The additive principal connection on the trivial bundle -/

/-- Pullback of the matrix work form to the total space `Base × ℝ`. -/
def liftedWorkForm : (Base n × ℝ) →L[ℝ] (Base n × ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Base n × ℝ) (Base n) ℝ).flip
      (ContinuousLinearMap.fst ℝ (Base n) ℝ)).comp
    (workForm.comp (ContinuousLinearMap.fst ℝ (Base n) ℝ))

@[simp] theorem liftedWorkForm_apply (p V : Base n × ℝ) :
    liftedWorkForm p V = workForm p.1 V.1 := rfl

/-- The additive connection one-form `Θ_(x,w)(v,z) = z - α_x(v)`. -/
def connectionForm (p : Base n × ℝ) : (Base n × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ (Base n) ℝ - liftedWorkForm p

@[simp] theorem connectionForm_apply (p V : Base n × ℝ) :
    connectionForm p V = V.2 - workForm p.1 V.1 := rfl

/-- The connection reproduces the additive Lie algebra on vertical vectors. -/
@[simp] theorem connectionForm_vertical (p : Base n × ℝ) (z : ℝ) :
    connectionForm p (0, z) = z := by
  simp

/-- Fiber translations preserve the connection form. Their derivative is the
identity, and the displayed form is independent of the fiber coordinate. -/
theorem connectionForm_fiber_translation (x : Base n) (w c : ℝ) :
    connectionForm (x, w + c) = connectionForm (x, w) := rfl

theorem hasFDerivAt_connectionForm (p : Base n × ℝ) :
    HasFDerivAt (connectionForm (n := n)) (-liftedWorkForm) p := by
  exact liftedWorkForm.hasFDerivAt.const_sub
    (ContinuousLinearMap.snd ℝ (Base n) ℝ)

/-- The additive principal curvature is the negative of `dα`, with this
work-on convention. Both sides are derived from the actual one-form. -/
theorem connectionForm_alternating_fderiv (p V W : Base n × ℝ) :
    fderiv ℝ (connectionForm (n := n)) p V W -
        fderiv ℝ (connectionForm (n := n)) p W V =
      -workCurvature V.1 W.1 := by
  rw [(hasFDerivAt_connectionForm p).fderiv]
  change -workForm V.1 W.1 - -workForm W.1 V.1 =
    -(workForm V.1 W.1 - workForm W.1 V.1)
  exact (neg_sub_neg (workForm V.1 W.1) (workForm W.1 V.1)).trans
    (neg_sub (workForm V.1 W.1) (workForm W.1 V.1)).symm

/-! ## Matrix paths and their constructed horizontal lifts -/

/-- Pullback of the work form along a path with a specified velocity. -/
def workCurrent (path velocity : ℝ → Base n) (t : ℝ) : ℝ :=
  workForm (path t) (velocity t)

@[simp] theorem workCurrent_apply (path velocity : ℝ → Base n) (t : ℝ) :
    workCurrent path velocity t = Matrix.trace ((path t).1 * (velocity t).2) := rfl

theorem continuous_workCurrent (path velocity : ℝ → Base n)
    (hpath : Continuous path) (hvelocity : Continuous velocity) :
    Continuous (workCurrent path velocity) :=
  (workForm.continuous.comp hpath).clm_apply hvelocity

/-- The lift is constructed by integrating the actual pulled-back current. -/
def horizontalLift (path velocity : ℝ → Base n) (a w : ℝ) (t : ℝ) :
    Base n × ℝ :=
  (path t, workOnLift (workCurrent path velocity) a w t)

/-- The derivative of the constructed total-space lift, obtained from the
actual base-path derivative and native interval FTC. -/
theorem hasDerivAt_horizontalLift (path velocity : ℝ → Base n)
    (hcurrent : Continuous (workCurrent path velocity)) (a w t : ℝ)
    (hpath : HasDerivAt path (velocity t) t) :
    HasDerivAt (horizontalLift path velocity a w)
      (velocity t, workCurrent path velocity t) t :=
  hpath.prodMk (hasDerivAt_workOnLift _ hcurrent a w t)

/-- The actual derivative of the lift lies in the kernel of the connection. -/
theorem horizontalLift_horizontal (path velocity : ℝ → Base n)
    (hcurrent : Continuous (workCurrent path velocity)) (a w t : ℝ)
    (hpath : HasDerivAt path (velocity t) t) :
    connectionForm (horizontalLift path velocity a w t)
      (deriv (horizontalLift path velocity a w) t) = 0 := by
  rw [(hasDerivAt_horizontalLift path velocity hcurrent a w t hpath).deriv]
  change workForm (path t) (velocity t) - workForm (path t) (velocity t) = 0
  exact sub_self _

/-! ## A noncommuting real matrix curvature witness -/

open InfoGeometry.SplitQuaternion in
/-- Existing real split-quaternion generators give symmetric density and
Hamiltonian directions with a nonzero commutator and nonzero work curvature.
The density direction is trace zero, as required in a trace-one density slice. -/
theorem splitQuaternion_noncommuting_curvature_witness :
    let R := splitK
    let A := splitK + splitJ
    R.transpose = R ∧ A.transpose = A ∧ Matrix.trace R = 0 ∧
      R * A ≠ A * R ∧
      workCurvature (R, 0) (0, A) = 2 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · simp only [Matrix.trace, Fin.sum_univ_two]
    change (1 : ℝ) + -1 = 0
    norm_num
  · intro h
    simp only [mul_add, add_mul, splitK_sq, splitK_mul_splitJ, splitJ_mul_splitK] at h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1)
      (add_left_cancel h)
    change (1 : ℝ) = -1 at h01
    norm_num at h01
  · rw [workCurvature_apply]
    simp only [zero_mul, sub_zero, mul_add,
      splitK_sq, splitK_mul_splitJ, Matrix.trace_add]
    simp only [Matrix.trace, Fin.sum_univ_two]
    change ((1 : ℝ) + 1) + (0 + 0) = 2
    norm_num

end InfoGeometry.Thermo.RealMatrixWorkConnection
