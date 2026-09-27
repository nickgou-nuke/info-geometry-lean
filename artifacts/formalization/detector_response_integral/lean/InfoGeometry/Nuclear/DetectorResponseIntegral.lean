import InfoGeometry.Nuclear.DetectorResponseCore
import InfoGeometry.Nuclear.ApollonianBipolarField

/-!
# Connection to the existing detector-flux owner

The repository's inverse-square flux is used LOCALLY inside the actual response
integral. Its radius varies with the interaction position. No theorem here
moves that radius outside the integral or asserts an exact VPD collapse.
-/

noncomputable section

namespace InfoGeometry.Nuclear.DetectorResponseIntegral

open Set MeasureTheory
open InfoGeometry.Nuclear.DetectorTransportKernel
open InfoGeometry.Nuclear.DetectorVolumeResponse
open InfoGeometry.Nuclear.DetectorBeerLambert

/-- Reuse the existing local isotropic flux, with a separately integrated
first-collision path density. -/
theorem firstCollisionKernel_eq_existing_flux {μ d : ℝ} {p : Point}
    (hd : 0 < d) (hz : 0 ≤ p.2) :
    firstCollisionKernel μ d p =
      ApollonianBipolarField.fluxDensity 1 (sourceRange d p) Real.pi *
        collisionDensity μ (materialPath d p) := by
  unfold firstCollisionKernel ApollonianBipolarField.fluxDensity collisionDensity
  rw [sourceRange_sq hd hz]
  ring

/-- The old flux is an integrand factor, not an asserted formula for the
integrated detector efficiency. -/
theorem response_eq_existing_flux_integral (μ d R L : ℝ) (hd : 0 < d)
    (κ : Point → ℝ) :
    response μ d R L κ =
      ∫ p in cylinder R L,
        (ApollonianBipolarField.fluxDensity 1 (sourceRange d p) Real.pi *
          collisionDensity μ (materialPath d p)) * κ p := by
  apply setIntegral_congr_fun (measurableSet_cylinder R L)
  intro p hp
  rw [firstCollisionKernel_eq_existing_flux hd hp.2.1]

/-- On the axis, the existing separation d + z is the radius of EACH local
interaction point; z remains an integration variable. -/
theorem on_axis_kernel_uses_existing_separation {μ d z : ℝ}
    (hd : 0 < d) (hz : 0 ≤ z) :
    firstCollisionKernel μ d ((0, 0), z) =
      ApollonianBipolarField.fluxDensity (collisionDensity μ z)
        (ApollonianBipolarField.interPolarDist d z) Real.pi := by
  unfold firstCollisionKernel
  rw [materialPath_on_axis hd hz, ApollonianBipolarField.inter_polar_dist_eq]
  simp [rangeSq, ApollonianBipolarField.fluxDensity, collisionDensity]

end InfoGeometry.Nuclear.DetectorResponseIntegral
