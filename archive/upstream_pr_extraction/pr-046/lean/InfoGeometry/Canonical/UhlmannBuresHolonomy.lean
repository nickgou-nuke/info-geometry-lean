import InfoGeometry.Canonical.CertifiedModularReduction
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.Holonomy

variable {H₂ : Type*}
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable (c : CertifiedModularReduction (E := H₂))

local notation "EndH" => H₂ →L[ℝ] H₂

/--
Owner obstruction `χ` for holonomy/curvature on the property lane.

This is the property spectral/metric anomaly, not the ambient commutator
`[Kambient, Preg]` (which is structurally zero on the support-compressed lane).
-/
@[rep_depth operator]
noncomputable def χ : EndH :=
  c.anomaly

/--
`χ = 0` iff spectral and metric supports are aligned.
-/
@[rep_depth operator]
theorem chi_zero_iff_alignment :
    χ c = 0 ↔ c.SpectralMetricAlignment := by
  simpa [χ] using c.anomaly_vanishes_iff_alignment

/--
Uhlmann/Bures-style curvature shadow on the regular lane.
-/
@[rep_depth operator]
noncomputable def uhlmannCurvature : EndH :=
  c.Preg * χ c * χ c * c.Preg

/--
Second-order defect scattering operator using the physical generator `Kphys`.
-/
@[rep_depth operator]
noncomputable def defectScattering : EndH :=
  c.Preg * c.Kphys * c.Pzero * c.Kphys * c.Preg

/--
In the inertial lane (`χ = 0`), the curvature shadow vanishes.
-/
@[rep_depth operator]
theorem zero_curvature_of_inertial_regular_lane
    (hInertial : c.InertialRegularLane) :
    uhlmannCurvature c = 0 := by
  have hChi : χ c = 0 := by
    simpa [χ, CertifiedModularReduction.InertialRegularLane] using hInertial
  simp [uhlmannCurvature, hChi]

/--
In the inertial lane, there is no second-order defect scattering.
-/
@[rep_depth operator]
theorem zero_defect_scattering_of_inertial_regular_lane
    (hInertial : c.InertialRegularLane) :
    defectScattering c = 0 := by
  have hKill := c.Kphys_kills_Pzero_of_inertial_regular_lane hInertial
  unfold defectScattering
  calc
    c.Preg * c.Kphys * c.Pzero * c.Kphys * c.Preg
        = c.Preg * c.Kphys * (c.Pzero * c.Kphys) * c.Preg := by simp [mul_assoc]
    _ = c.Preg * c.Kphys * 0 * c.Preg := by rw [hKill.1]
    _ = 0 := by simp

/--
In the inertial lane, curvature equals negative defect scattering (both vanish).
-/
@[rep_depth operator]
theorem curvature_eq_neg_defectScattering_of_inertial_regular_lane
    (hInertial : c.InertialRegularLane) :
    uhlmannCurvature c = -defectScattering c := by
  have hCurv : uhlmannCurvature c = 0 :=
    zero_curvature_of_inertial_regular_lane (c := c) hInertial
  have hScatt : defectScattering c = 0 :=
    zero_defect_scattering_of_inertial_regular_lane (c := c) hInertial
  calc
    uhlmannCurvature c = 0 := hCurv
    _ = -defectScattering c := by simp [hScatt]

end InfoGeometry.Canonical.Holonomy
