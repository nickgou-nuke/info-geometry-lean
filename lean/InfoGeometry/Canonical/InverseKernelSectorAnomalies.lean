/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.Singular
import InfoGeometry.Core.JordanAssociator
import InfoGeometry.Singular.MoorePenroseSectors

/-!
# Inverse-kernel sectors retaining chiral and Einstein anomalies

The spectral projector is generally oblique. No commutation of Drazin and MP
supports is assumed here. The left and right anomalies have the orientation
defined in `CertifiedInverseKernel`; the Einstein anomaly has the opposite
orientation to the right anomaly. Products remain associative, whereas the
special Jordan product has a double-commutator associator.
-/

noncomputable section
namespace InfoGeometry.Canonical.CertifiedInverseKernel

open InfoGeometry.Singular.ProjectionSectors
open InfoGeometry.Singular.MetricAlgebraicProjectionDefect
open InfoGeometry.Core.JordanPeirceDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (K : CertifiedInverseKernel E)

/-- The ordered left-sector sum differs from identity by the existing left anomaly. -/
theorem spectral_metric_sector_sum :
    K.spectralProjector * K.metricProjector +
      (K.spectralProjector - K.metricProjector)^2 +
      (1 - K.spectralProjector) * (1 - K.metricProjector) = 1 + K.chiralAnomaly := by
  exact three_sector_sum_with_defect K.spectralProjector_idempotent K.metricProjector_idempotent

/-- The right-sector sum retains the opposite of the Einstein anomaly. -/
theorem spectral_range_sector_sum :
    K.spectralProjector * K.mpRangeProjector +
      (K.spectralProjector - K.mpRangeProjector)^2 +
      (1 - K.spectralProjector) * (1 - K.mpRangeProjector) =
      1 - EinsteinAnomaly K.A K.A_MP K.A_D := by
  have h := three_sector_sum_with_defect
    K.spectralProjector_idempotent K.mpRangeProjector_idempotent
  change _ = 1 + (K.spectralProjector * K.mpRangeProjector -
    K.mpRangeProjector * K.spectralProjector) at h
  rw [h]
  change 1 + ((K.A * K.A_D) * (K.A * K.A_MP) -
    (K.A * K.A_MP) * (K.A * K.A_D)) = _
  unfold EinsteinAnomaly
  noncomm_ring

/-- The putative joint spectral/metric interior has an explicit anomaly defect. -/
theorem spectral_metric_interior_idempotence_defect :
    (K.spectralProjector * K.metricProjector)^2 -
      K.spectralProjector * K.metricProjector =
      -K.spectralProjector * K.chiralAnomaly * K.metricProjector := by
  exact refinement_idempotence_defect K.spectralProjector_idempotent K.metricProjector_idempotent

/-- Drazin transport of the MP boundary expression detects both anomaly channels. -/
theorem spectral_commutator_mp_boundary_square :
    K.spectralProjector * (K.mpRangeProjector - K.metricProjector)^2 -
      (K.mpRangeProjector - K.metricProjector)^2 * K.spectralProjector =
      (K.rightChiralAnomaly - K.chiralAnomaly) *
        (K.mpRangeProjector - K.metricProjector) +
      (K.mpRangeProjector - K.metricProjector) *
        (K.rightChiralAnomaly - K.chiralAnomaly) := by
  change K.spectralProjector * (K.mpRangeProjector - K.metricProjector)^2 -
      (K.mpRangeProjector - K.metricProjector)^2 * K.spectralProjector =
    ((K.spectralProjector * K.mpRangeProjector - K.mpRangeProjector * K.spectralProjector) -
      (K.spectralProjector * K.metricProjector - K.metricProjector * K.spectralProjector)) *
        (K.mpRangeProjector - K.metricProjector) +
      (K.mpRangeProjector - K.metricProjector) *
        ((K.spectralProjector * K.mpRangeProjector - K.mpRangeProjector * K.spectralProjector) -
          (K.spectralProjector * K.metricProjector - K.metricProjector * K.spectralProjector))
  noncomm_ring

/-- In a triple Jordan product the left anomaly drives the associator. -/
theorem spectral_metric_jordan_associator (Y : E →L[ℝ] E) :
    jordanMul (jordanMul K.spectralProjector Y) K.metricProjector -
      jordanMul K.spectralProjector (jordanMul Y K.metricProjector) =
      (1 / 4 : ℝ) • (Y * K.chiralAnomaly - K.chiralAnomaly * Y) := by
  exact InfoGeometry.Core.JordanAssociator.jordan_associator_eq_expanded_double_commutator
    K.spectralProjector Y K.metricProjector

/-- The opposite convention for the Einstein anomaly fixes the Jordan associator sign. -/
theorem range_spectral_jordan_associator (Y : E →L[ℝ] E) :
    jordanMul (jordanMul K.mpRangeProjector Y) K.spectralProjector -
      jordanMul K.mpRangeProjector (jordanMul Y K.spectralProjector) =
      (1 / 4 : ℝ) • (Y * EinsteinAnomaly K.A K.A_MP K.A_D -
        EinsteinAnomaly K.A K.A_MP K.A_D * Y) := by
  exact InfoGeometry.Core.JordanAssociator.jordan_associator_eq_expanded_double_commutator
    K.mpRangeProjector Y K.spectralProjector

end InfoGeometry.Canonical.CertifiedInverseKernel
