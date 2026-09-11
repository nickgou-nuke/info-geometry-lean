import InfoGeometry.Canonical.SouriauGeometricQuantizationTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Coordinate curvature normalization for the concrete symplectic plane

The canonical trivial line bundle over the standard symplectic plane admits the
Liouville-type potential `A_p(Y) = ℏ⁻¹ p₀ Y₁`.  Its antisymmetrized derivative
is exactly `ℏ⁻¹ ω`.  This is a finite coordinate normalization theorem; it
does not construct a connection on a line bundle.
-/

namespace InfoGeometry.Canonical

section Connection

variable (hbar : ℝ) (hh : hbar ≠ 0)

/-- Liouville-type connection potential in the standard plane chart. -/
noncomputable def standardPlaneConnection (p X : SymplecticPlane) : ℝ :=
  hbar⁻¹ * (p 0 * X 1)

/-- Antisymmetrized coordinate derivative of the connection potential. -/
noncomputable def standardPlaneCurvature (X Y : SymplecticPlane) : ℝ :=
  standardPlaneConnection hbar X Y - standardPlaneConnection hbar Y X

theorem standardPlaneConnection_add_right (p X Y : SymplecticPlane) :
    standardPlaneConnection hbar p (X + Y) =
      standardPlaneConnection hbar p X + standardPlaneConnection hbar p Y := by
  simp [standardPlaneConnection]
  ring

theorem standardPlaneConnection_smul_right (a : ℝ) (p X : SymplecticPlane) :
    standardPlaneConnection hbar p (a • X) =
      a * standardPlaneConnection hbar p X := by
  simp [standardPlaneConnection]
  ring

theorem continuous_standardPlaneConnection (X : SymplecticPlane) :
    Continuous (fun p : SymplecticPlane => standardPlaneConnection hbar p X) := by
  unfold standardPlaneConnection
  fun_prop

theorem standardPlaneCurvature_eq_scaled_form (X Y : SymplecticPlane) :
    standardPlaneCurvature hbar X Y =
      hbar⁻¹ * standardPlaneFormFun X Y := by
  simp [standardPlaneCurvature, standardPlaneConnection, standardPlaneFormFun]
  ring

theorem hbar_mul_standardPlaneCurvature (hh : hbar ≠ 0) (X Y : SymplecticPlane) :
    hbar * standardPlaneCurvature hbar X Y =
      standardSymplecticPlaneLeaf.form X Y := by
  rw [standardPlaneCurvature_eq_scaled_form]
  change hbar * (hbar⁻¹ * standardPlaneFormFun X Y) = standardPlaneFormFun X Y
  field_simp

theorem standardPlaneCurvature_matches_scaled_curvature
    (X Y : SymplecticPlane) :
    standardPlaneCurvature hbar X Y =
      (standardPlaneScaledCurvature hbar hh).curvature X Y := by
  rw [standardPlaneCurvature_eq_scaled_form]
  change hbar⁻¹ * standardPlaneFormFun X Y =
    (hbar⁻¹ • standardPlaneForm) X Y
  rfl

end Connection

end InfoGeometry.Canonical
