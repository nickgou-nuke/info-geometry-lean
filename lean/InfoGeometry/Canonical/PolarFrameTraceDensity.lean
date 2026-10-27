/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FiniteBogoliubovFrameDeformationEntropy
import Mathlib.Analysis.Matrix.PosDef

/-!
# Trace densities of positive polar frame operators

An arbitrary strictly positive complex matrix defines a faithful positive
functional by `X ↦ trace (P * X)`.  The trace pairing uniquely determines its
density.  Trace normalization shifts the negative operator logarithm by a
central scalar; its commutators therefore remain unchanged.

The last section applies these facts to the existing positive polar distortion
of an arbitrary invertible relative frame.  The reference is the ordinary
finite matrix trace.  No commutation hypothesis is imposed on the arguments.
-/

noncomputable section

namespace InfoGeometry.Canonical.PolarFrameTraceDensity

open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The complex linear functional with trace-relative density `P`. -/
def traceDensityLinear (P : Mat) : Mat →ₗ[ℂ] ℂ where
  toFun X := Matrix.trace (P * X)
  map_add' X Y := by simp [mul_add, Matrix.trace_add]
  map_smul' c X := by simp [Matrix.trace_smul]

@[simp] theorem traceDensityLinear_apply (P X : Mat) :
    traceDensityLinear P X = Matrix.trace (P * X) := rfl

/-- Cyclic trace exposes the positive square-root congruence. -/
theorem trace_mul_eq_trace_sqrt_conjugate (P X : Mat) (hP : 0 ≤ P) :
    Matrix.trace (P * X) =
      Matrix.trace (CFC.sqrt P * X * CFC.sqrt P) := by
  rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self P hP]

/-- A positive matrix is a positive density on the full matrix algebra. -/
theorem traceDensityLinear_nonneg (P X : Mat) (hP : 0 ≤ P) (hX : 0 ≤ X) :
    0 ≤ traceDensityLinear P X := by
  rw [traceDensityLinear_apply, trace_mul_eq_trace_sqrt_conjugate P X hP]
  exact (conjugate_nonneg_of_nonneg hX (CFC.sqrt_nonneg P)).posSemidef.trace_nonneg

/-- The trace-density functional, bundled as a native positive linear map. -/
def positiveTraceDensity (P : Mat) (hP : 0 ≤ P) : Mat →ₚ[ℂ] ℂ :=
  .mk₀ (traceDensityLinear P) (fun X hX => traceDensityLinear_nonneg P X hP hX)

@[simp] theorem positiveTraceDensity_apply (P X : Mat) (hP : 0 ≤ P) :
    positiveTraceDensity P hP X = Matrix.trace (P * X) := rfl

/-- The full trace pairing determines the density uniquely. -/
theorem traceDensityLinear_injective :
    Function.Injective (traceDensityLinear (n := n)) := by
  intro P Q h
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  exact congrArg (fun f : Mat →ₗ[ℂ] ℂ => f X) h

theorem traceDensityLinear_eq_iff (P Q : Mat) :
    traceDensityLinear P = traceDensityLinear Q ↔ P = Q :=
  traceDensityLinear_injective.eq_iff

/-- A strictly positive density is faithful on all positive matrix inputs. -/
theorem traceDensityLinear_eq_zero_iff (P X : Mat)
    (hP : IsStrictlyPositive P) (hX : 0 ≤ X) :
    traceDensityLinear P X = 0 ↔ X = 0 := by
  rw [traceDensityLinear_apply, trace_mul_eq_trace_sqrt_conjugate P X hP.nonneg]
  have hS : IsUnit (CFC.sqrt P) :=
    (CFC.isUnit_sqrt_iff P hP.nonneg).mpr hP.isUnit
  have hconj : 0 ≤ CFC.sqrt P * X * CFC.sqrt P :=
    conjugate_nonneg_of_nonneg hX (CFC.sqrt_nonneg P)
  rw [hconj.posSemidef.trace_eq_zero_iff]
  constructor
  · intro h
    apply hS.mul_left_cancel
    apply hS.mul_right_cancel
    simpa using h
  · rintro rfl
    simp

/-- The unnormalized mass of a trace density. -/
def traceMass (P : Mat) : ℝ := (Matrix.trace P).re

theorem traceMass_pos [Nonempty n] (P : Mat) (hP : IsStrictlyPositive P) :
    0 < traceMass P :=
  (RCLike.pos_iff.mp hP.posDef.trace_pos).1

/-- Normalization uses the trace mass and preserves the matrix carrier. -/
def normalizedDensity (P : Mat) : Mat := (traceMass P)⁻¹ • P

theorem normalizedDensity_isStrictlyPositive [Nonempty n]
    (P : Mat) (hP : IsStrictlyPositive P) :
    IsStrictlyPositive (normalizedDensity P) :=
  IsStrictlyPositive.smul (inv_pos.mpr (traceMass_pos P hP)) hP

theorem trace_normalizedDensity [Nonempty n]
    (P : Mat) (hP : IsStrictlyPositive P) :
    Matrix.trace (normalizedDensity P) = 1 := by
  have hmass : (Matrix.trace P).re ≠ 0 := ne_of_gt (traceMass_pos P hP)
  have him : (Matrix.trace P).im = 0 :=
    (RCLike.pos_iff.mp hP.posDef.trace_pos).2
  apply Complex.ext
  · simp [normalizedDensity, Matrix.trace_smul, traceMass, hmass]
  · simp [normalizedDensity, Matrix.trace_smul, him]

/-- The normalized positive functional sends the identity to one. -/
theorem normalizedDensity_functional_one [Nonempty n]
    (P : Mat) (hP : IsStrictlyPositive P) :
    positiveTraceDensity (normalizedDensity P)
      (normalizedDensity_isStrictlyPositive P hP).nonneg 1 = 1 := by
  simpa using trace_normalizedDensity P hP

/-- Normalization adds exactly a central scalar to the negative CFC logarithm. -/
theorem neg_log_normalizedDensity [Nonempty n]
    (P : Mat) (hP : IsStrictlyPositive P) :
    -CFC.log (normalizedDensity P) =
      -CFC.log P + Real.log (traceMass P) • (1 : Mat) := by
  rw [normalizedDensity, CFC.log_smul' P (inv_pos.mpr (traceMass_pos P hP)) hP,
    Real.log_inv, map_neg, Algebra.algebraMap_eq_smul_one]
  abel

/-- The central normalization shift leaves every operator commutator unchanged. -/
theorem neg_log_normalizedDensity_commutator [Nonempty n]
    (P X : Mat) (hP : IsStrictlyPositive P) :
    (-CFC.log (normalizedDensity P)) * X - X * (-CFC.log (normalizedDensity P)) =
      (-CFC.log P) * X - X * (-CFC.log P) := by
  rw [neg_log_normalizedDensity P hP]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

/-- The scalar trace readout records the dimension-dependent normalization shift. -/
theorem trace_neg_log_normalizedDensity [Nonempty n]
    (P : Mat) (hP : IsStrictlyPositive P) :
    (Matrix.trace (-CFC.log (normalizedDensity P))).re =
      (Matrix.trace (-CFC.log P)).re +
        Fintype.card n * Real.log (traceMass P) := by
  rw [neg_log_normalizedDensity P hP]
  simp [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, mul_comm]

open FiniteBogoliubovFrameDeformationEntropy

/-- The existing polar relative-frame operator determines a faithful trace density. -/
def polarFrameFunctional (F : FramePair (n := n)) : Mat →ₚ[ℂ] ℂ :=
  positiveTraceDensity F.polarVolumeOperator F.polarVolumeOperator_isStrictlyPositive.nonneg

@[simp] theorem polarFrameFunctional_apply (F : FramePair (n := n)) (X : Mat) :
    polarFrameFunctional F X = Matrix.trace (F.polarVolumeOperator * X) := rfl

theorem polarFrameFunctional_faithful (F : FramePair (n := n))
    (X : Mat) (hX : 0 ≤ X) : polarFrameFunctional F X = 0 ↔ X = 0 :=
  traceDensityLinear_eq_zero_iff F.polarVolumeOperator X
    F.polarVolumeOperator_isStrictlyPositive hX

/-- The existing deformation surprisal is the negative logarithm before normalization. -/
theorem normalized_polar_surprisal [Nonempty n] (F : FramePair (n := n)) :
    -CFC.log (normalizedDensity F.polarVolumeOperator) =
      F.deformationSurprisalOperator +
        Real.log (traceMass F.polarVolumeOperator) • (1 : Mat) :=
  neg_log_normalizedDensity F.polarVolumeOperator F.polarVolumeOperator_isStrictlyPositive

/-- The normalized polar density records the deformation readout plus its normalization correction. -/
theorem trace_normalized_polar_surprisal [Nonempty n] (F : FramePair (n := n)) :
    (Matrix.trace (-CFC.log (normalizedDensity F.polarVolumeOperator))).re =
      -Real.log ‖F.relativeVielbein.det‖ +
        Fintype.card n * Real.log (traceMass F.polarVolumeOperator) := by
  rw [trace_neg_log_normalizedDensity F.polarVolumeOperator
    F.polarVolumeOperator_isStrictlyPositive]
  exact congrArg (fun t : ℝ => t + Fintype.card n * Real.log (traceMass F.polarVolumeOperator))
    (trace_deformationSurprisalOperator F)

end InfoGeometry.Canonical.PolarFrameTraceDensity
