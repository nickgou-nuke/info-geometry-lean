import InfoGeometry.Canonical.MongeAmpereDualSheetBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.QuantumGeometryDualSheetBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.MongeAmpereDualSheetBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Repo-native quantum-geometry readout on the base carrier. -/
noncomputable def quantumGeometryOp (H : HessianGeometry E) (x : E) : E →L[ℝ] E :=
  H.metricOp x

/--
Operator-valued Cramer-Rao and quantum-geometry readouts coincide on the base carrier.
This stays on the operator level and does not pass through determinant or scalar volume
surfaces.
-/
theorem cramerRaoMetricOp_eq_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    cramerRaoMetricOp H x = quantumGeometryOp H x := rfl

/--
The doubled Cramer-Rao operator is the doubled lift of the owned quantum-geometry
operator.
-/
theorem dualSheetMetricOp_eq_dualSheetLift_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    dualSheetMetricOp (E := E) H x
      =
    dualSheetLift (E := E) (quantumGeometryOp H x) := by
  rfl

/--
The doubled Cramer-Rao operator is also the doubled lift of the base-carrier
Cramer-Rao operator.
-/
theorem dualSheetMetricOp_eq_dualSheetLift_cramerRaoMetricOp
    (H : HessianGeometry E) (x : E) :
    dualSheetMetricOp (E := E) H x
      =
    dualSheetLift (E := E) (cramerRaoMetricOp H x) := by
  rfl

@[simp] theorem plusBlockMap_dualSheetLift_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    plusBlockMap (E := E)
        (dualSheetLift (E := E) (quantumGeometryOp H x))
      =
    quantumGeometryOp H x := by
  exact plusBlockMap_dualSheetMetricOp (E := E) (H := H) (x := x)

@[simp] theorem minusBlockMap_dualSheetLift_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    minusBlockMap (E := E)
        (dualSheetLift (E := E) (quantumGeometryOp H x))
      =
    quantumGeometryOp H x := by
  exact minusBlockMap_dualSheetMetricOp (E := E) (H := H) (x := x)

@[simp] theorem plusToMinusBlockMap_dualSheetLift_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    plusToMinusBlockMap (E := E)
        (dualSheetLift (E := E) (quantumGeometryOp H x))
      = 0 := by
  exact plusToMinusBlockMap_dualSheetMetricOp (E := E) (H := H) (x := x)

@[simp] theorem minusToPlusBlockMap_dualSheetLift_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    minusToPlusBlockMap (E := E)
        (dualSheetLift (E := E) (quantumGeometryOp H x))
      = 0 := by
  exact minusToPlusBlockMap_dualSheetMetricOp (E := E) (H := H) (x := x)

@[simp] theorem plusProjectorFlux_dualSheetLift_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    plusProjectorFlux
        (dualSheetLift (E := E) (quantumGeometryOp H x))
      = 0 := by
  exact plusProjectorFlux_dualSheetMetricOp (E := E) (H := H) (x := x)

@[simp] theorem minusProjectorFlux_dualSheetLift_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    minusProjectorFlux
        (dualSheetLift (E := E) (quantumGeometryOp H x))
      = 0 := by
  exact minusProjectorFlux_dualSheetMetricOp (E := E) (H := H) (x := x)

/--
Both base-carrier operator owners induce the same doubled operatorial geometry.
-/
theorem dualSheetLift_cramerRaoMetricOp_eq_dualSheetLift_quantumGeometryOp
    (H : HessianGeometry E) (x : E) :
    dualSheetLift (E := E) (cramerRaoMetricOp H x)
      =
    dualSheetLift (E := E) (quantumGeometryOp H x) := by
  rw [cramerRaoMetricOp_eq_quantumGeometryOp]

end InfoGeometry.Canonical.QuantumGeometryDualSheetBridge
