/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
import InfoGeometry.Analysis.PositiveMatrixDikin
import InfoGeometry.Canonical.PolarFrameTraceDensity
import InfoGeometry.Geometry.LegendreDifferential

/-!
# Native logdet Hessians, Dikin geometry, and relative polar deformation

The potential is the actual scalar function `P ↦ -log ‖det P‖`.  Its native
Fréchet Hessian is identified with the ordered inverse/trace form.  On the
strictly positive cone, arbitrary self-adjoint directions satisfy the cubic
self-concordance estimate, the dimension-dependent gradient bound, and the
Dikin cone-containment theorem.

These results apply directly to the positive polar operator of the existing
relative-frame construction.  The affine variation is in that positive
operator; no Hessian pullback through the nonlinear polar map is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorLogDetDikinGeometry

open InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
open InfoGeometry.Analysis.PositiveMatrixDikin
open InfoGeometry.Geometry.LegendreDifferential
open InfoGeometry.Canonical.FiniteBogoliubovFrameDeformationEntropy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The existing native Hessian map is the actual ordered logdet Hessian. -/
theorem hessianMap_negLogDet (P K H : Mat) (hP : IsUnit P) :
    hessianMap negLogDet P K H =
      (Matrix.trace (P⁻¹ * K * P⁻¹ * H)).re :=
  fderiv2_negLogDet_apply P K H hP

/-- The native Hessian is symmetric without a commutation assumption. -/
theorem hessianMap_negLogDet_symmetric (P K H : Mat) (hP : IsUnit P) :
    hessianMap negLogDet P K H = hessianMap negLogDet P H K := by
  rw [hessianMap_negLogDet P K H hP, hessianMap_negLogDet P H K hP]
  exact logDetHessian_symmetric P K H

/-- The concrete Dikin quadratic is exactly the native Hessian diagonal. -/
theorem hessianMap_negLogDet_self (P H : Mat) (hP : IsUnit P) :
    hessianMap negLogDet P H H = traceQuadratic P H := by
  rw [hessianMap_negLogDet P H H hP]
  simp only [traceQuadratic, reTrace, pow_two, mul_assoc]

/-- Positivity is proved for every self-adjoint tangent direction. -/
theorem hessianMap_negLogDet_nonneg {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    0 ≤ hessianMap negLogDet P H H := by
  rw [hessianMap_negLogDet_self P H hP.isUnit]
  exact traceQuadratic_nonneg hP hH

/-- The native Hessian is nondegenerate on the full self-adjoint tangent space. -/
theorem hessianMap_negLogDet_self_eq_zero_iff {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    hessianMap negLogDet P H H = 0 ↔ H = 0 := by
  rw [hessianMap_negLogDet_self P H hP.isUnit]
  exact traceQuadratic_eq_zero_iff hP hH

theorem hessianMap_negLogDet_pos_iff {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    0 < hessianMap negLogDet P H H ↔ H ≠ 0 := by
  constructor
  · intro hpos hzero
    have h := (hessianMap_negLogDet_self_eq_zero_iff hP hH).mpr hzero
    rw [h] at hpos
    exact (lt_irrefl 0) hpos
  · intro hne
    apply lt_of_le_of_ne (hessianMap_negLogDet_nonneg hP hH)
    intro hzero
    exact hne ((hessianMap_negLogDet_self_eq_zero_iff hP hH).mp hzero.symm)

/-- The actual second line derivative agrees with the native Hessian diagonal. -/
theorem second_deriv_eq_hessianMap (P H : Mat) (hP : IsUnit P) :
    deriv (deriv (fun t : ℝ => negLogDet (P + t • H))) 0 =
      hessianMap negLogDet P H H := by
  rw [second_deriv_negLogDet_add_smul_zero P H hP,
    hessianMap_negLogDet_self P H hP]
  rfl

/-- Self-concordance for actual iterated derivatives of the scalar potential. -/
theorem native_logDet_selfConcordance {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    |deriv (deriv (deriv (fun t : ℝ => negLogDet (P + t • H)))) 0| ≤
      2 * (hessianMap negLogDet P H H) ^ (3 / 2 : ℝ) := by
  rw [third_deriv_negLogDet_add_smul_zero P H hP.isUnit,
    hessianMap_negLogDet_self P H hP.isUnit]
  change |(-2 : ℝ) * traceCubic P H| ≤ 2 * traceQuadratic P H ^ (3 / 2 : ℝ)
  rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  exact mul_le_mul_of_nonneg_left (abs_traceCubic_le hP hH) (by norm_num)

/-- The native gradient obeys the ordinary-trace dimension bound. -/
theorem native_logDet_gradient_bound {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    |fderiv ℝ negLogDet P H| ≤ Real.sqrt (Fintype.card n : ℝ) *
      Real.sqrt (hessianMap negLogDet P H H) := by
  rw [fderiv_negLogDet_apply P H hP.isUnit,
    hessianMap_negLogDet_self P H hP.isUnit, abs_neg]
  exact abs_reTrace_inv_mul_le_sqrt_card_mul_sqrt_traceQuadratic hP hH

/-- Two-sided operator-order control uses the actual Hessian radius. -/
theorem native_logDet_dikin_order_bounds {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H) :
    (1 - Real.sqrt (hessianMap negLogDet P H H)) • P ≤ P + H ∧
      P + H ≤ (1 + Real.sqrt (hessianMap negLogDet P H H)) • P := by
  rw [hessianMap_negLogDet_self P H hP.isUnit]
  exact dikin_order_bounds hP hH

/-- The actual Hessian unit ellipsoid stays inside the strictly positive cone. -/
theorem native_logDet_dikin_containment {P H : Mat}
    (hP : IsStrictlyPositive P) (hH : IsSelfAdjoint H)
    (hsmall : hessianMap negLogDet P H H < 1) :
    IsStrictlyPositive (P + H) := by
  rw [hessianMap_negLogDet_self P H hP.isUnit] at hsmall
  exact isStrictlyPositive_add_of_traceQuadratic_lt_one hP hH hsmall

/-- Point-centered form of the same ellipsoid containment. -/
theorem native_logDet_dikin_point_containment {P Q : Mat}
    (hP : IsStrictlyPositive P) (hQ : IsSelfAdjoint Q)
    (hsmall : hessianMap negLogDet P (Q - P) (Q - P) < 1) :
    IsStrictlyPositive Q := by
  have h := native_logDet_dikin_containment hP (hQ.sub hP.isSelfAdjoint) hsmall
  have heq : P + (Q - P) = Q := by abel
  rwa [heq] at h

/-- The scalar potential is the trace of the negative operator logarithm. -/
theorem negLogDet_eq_trace_neg_log (P : Mat) (hP : IsStrictlyPositive P) :
    negLogDet P = (Matrix.trace (-CFC.log P)).re := by
  simp only [negLogDet, Matrix.trace_neg, Complex.neg_re,
    trace_log_eq_log_norm_det_of_isStrictlyPositive P hP]

/-- The original relative-frame deformation readout is this positive-cone potential. -/
theorem negLogDet_polar_eq_trace_surprisal (F : FramePair (n := n)) :
    negLogDet F.polarVolumeOperator =
      (Matrix.trace F.deformationSurprisalOperator).re :=
  negLogDet_eq_trace_neg_log F.polarVolumeOperator F.polarVolumeOperator_isStrictlyPositive

theorem negLogDet_polar_eq_relative_volume (F : FramePair (n := n)) :
    negLogDet F.polarVolumeOperator = -Real.log ‖F.relativeVielbein.det‖ := by
  rw [negLogDet_polar_eq_trace_surprisal, trace_deformationSurprisalOperator]

/-- An arbitrary invertible relative frame supplies the positive base point automatically. -/
theorem polar_frame_native_selfConcordance (F : FramePair (n := n))
    {H : Mat} (hH : IsSelfAdjoint H) :
    |deriv (deriv (deriv (fun t : ℝ => negLogDet (F.polarVolumeOperator + t • H)))) 0| ≤
      2 * (hessianMap negLogDet F.polarVolumeOperator H H) ^ (3 / 2 : ℝ) :=
  native_logDet_selfConcordance F.polarVolumeOperator_isStrictlyPositive hH

/-- The same frame's positive polar operator has a concrete, proved Dikin neighborhood. -/
theorem polar_frame_native_dikin_containment (F : FramePair (n := n))
    {H : Mat} (hH : IsSelfAdjoint H)
    (hsmall : hessianMap negLogDet F.polarVolumeOperator H H < 1) :
    IsStrictlyPositive (F.polarVolumeOperator + H) :=
  native_logDet_dikin_containment F.polarVolumeOperator_isStrictlyPositive hH hsmall

end InfoGeometry.Canonical.OperatorLogDetDikinGeometry
