/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PenroseTwistorOperatorBridge
import InfoGeometry.Twistor.TwistorOperatorLift

/-!
# First-quantized Penrose operators on the native Zorn carrier

Transport the already-defined Penrose coordinate, derivative, and finite
boundary endomorphisms along the existing real-linear twistor/Zorn
equivalence. The resulting operators act on the native Zorn vector-matrix
carrier, and transport preserves the exact finite-boundary commutator.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwistorFirstQuantizedZornOperatorBridge

open InfoGeometry.Twistor.PenroseTwistorOperatorBridge
open InfoGeometry.Twistor.TwistorOperatorLift
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

local notation "ZV" => InfoGeometry.Twistor.RealSplitOctonionCarrierBridge.CanonicalZorn

/-- The two existing carrier equivalences, composed from paired Penrose
twistors through canonical Zorn coordinates to the native Zorn vector matrix. -/
def penroseToZornVectorEquiv :
    InfoGeometry.Twistor.PenroseIncidence.Twistor4 ≃ₗ[ℝ] ZV :=
  twistorRealEquivZorn

/-- Conjugate a real-linear operator on the Penrose carrier to the native
Zorn vector-matrix carrier using the established carrier equivalence. -/
def transportPenroseEnd (T : Module.End ℂ InfoGeometry.Twistor.PenroseIncidence.Twistor4) :
    Module.End ℝ ZV :=
  (penroseToZornVectorEquiv.toLinearMap.comp (T.restrictScalars ℝ)).comp
    penroseToZornVectorEquiv.symm.toLinearMap

/-- The transported operator acts by moving to the Penrose carrier, applying
the original operator, and moving back to the Zorn carrier. -/
theorem transportPenroseEnd_apply (T : Module.End ℂ InfoGeometry.Twistor.PenroseIncidence.Twistor4)
    (x : ZV) :
    transportPenroseEnd T x = penroseToZornVectorEquiv (T (penroseToZornVectorEquiv.symm x)) := rfl

/-- First-quantized Penrose coordinate acting on the native Zorn carrier. -/
def zornCoordinate : Module.End ℝ ZV :=
  transportPenroseEnd firstQuantizedCoordinate

/-- First-quantized Penrose derivative acting on the native Zorn carrier. -/
def zornDerivative : Module.End ℝ ZV :=
  transportPenroseEnd firstQuantizedDerivative

/-- The finite-boundary operator transported to the native Zorn carrier. -/
def zornBoundary : Module.End ℝ ZV :=
  transportPenroseEnd firstQuantizedBoundary

/-- The transported coordinate/derivative commutator is exactly the
transported Penrose boundary operator. -/
theorem zornCoordinate_commutator_eq_boundary :
    zornCoordinate * zornDerivative - zornDerivative * zornCoordinate = zornBoundary := by
  apply LinearMap.ext
  intro x
  dsimp [zornCoordinate, zornDerivative, zornBoundary, transportPenroseEnd]
  simp only [LinearEquiv.symm_apply_apply]
  change penroseToZornVectorEquiv
      (firstQuantizedCoordinate (firstQuantizedDerivative
        (penroseToZornVectorEquiv.symm x))) -
    penroseToZornVectorEquiv
      (firstQuantizedDerivative (firstQuantizedCoordinate
        (penroseToZornVectorEquiv.symm x))) =
    penroseToZornVectorEquiv
      (firstQuantizedBoundary (penroseToZornVectorEquiv.symm x))
  calc
    _ = penroseToZornVectorEquiv
        (firstQuantizedCoordinate (firstQuantizedDerivative
          (penroseToZornVectorEquiv.symm x)) -
          firstQuantizedDerivative (firstQuantizedCoordinate
            (penroseToZornVectorEquiv.symm x))) :=
      (penroseToZornVectorEquiv.map_sub _ _).symm
    _ = penroseToZornVectorEquiv
        (firstQuantizedBoundary (penroseToZornVectorEquiv.symm x)) :=
      congrArg penroseToZornVectorEquiv
        (LinearMap.congr_fun firstQuantized_commutator_eq_boundary
          (penroseToZornVectorEquiv.symm x))

end InfoGeometry.Twistor.TwistorFirstQuantizedZornOperatorBridge
