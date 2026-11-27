/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldBeltramiContact
import InfoGeometry.Canonical.ArnoldBeltramiVolume
import InfoGeometry.Canonical.ArnoldBeltramiVolumeCharacters
import InfoGeometry.Canonical.SmoothDiffeomorphismDensityOrbit
import InfoGeometry.Canonical.KLScaleItakuraSaito
import InfoGeometry.Projective.FisherRaoRadialShape
import InfoGeometry.Geometry.RealMatrixFisherRadial

/-!
# Real Arnold flow and information geometry

This integration surface connects the actual Beltrami flow to the native
measure action and its stabilizer. Its imports expose the independently
proved contact, cotangent determinant, Fisher mass/shape, matrix log-determinant
and KL radial identities. Their carriers and normalization conventions remain
explicit; no equivalence of unrelated entropy or Casimir foliations is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldInformationGeometry

open MeasureTheory
open scoped ENNReal
open InfoGeometry.Canonical.NavierStokesShearReconstruction
open InfoGeometry.Canonical.ArnoldBeltramiFlow

/-- Include the existing physical one-parameter group in the acting smooth
group, preserving its actual homeomorphisms and multiplication. -/
def smoothFlowHom (s : ℝ) : Multiplicative ℝ →* smoothDiffeomorphismSubgroup Space :=
  (Subgroup.inclusion (smoothVolumePreserving_le_smooth (volume : Measure Space))).comp
    (flowHom s)

/-- The native measure action of the actual flow fixes Lebesgue volume. -/
theorem smoothFlowHom_fixes_volume (s : ℝ) (t : Multiplicative ℝ) :
    smoothFlowHom s t • (volume : Measure Space) = volume := by
  change Measure.map (flowHomeomorph s t.toAdd) volume = volume
  exact (measurePreserving_flow s t.toAdd).map_eq

/-- The physical flow belongs to the stabilizer used by the measure-orbit
quotient, not merely to a similarly named algebraic structure. -/
theorem smoothFlowHom_mem_stabilizer (s : ℝ) (t : Multiplicative ℝ) :
    smoothFlowHom s t ∈
      MulAction.stabilizer (smoothDiffeomorphismSubgroup Space) (volume : Measure Space) :=
  smoothFlowHom_fixes_volume s t

/-- External scaling of the reference measure commutes with this physical
flow, so every constant multiple is also invariant. -/
theorem smoothFlowHom_fixes_scaled_volume (s : ℝ) (t : Multiplicative ℝ) (c : ℝ≥0∞) :
    smoothFlowHom s t • (c • (volume : Measure Space)) = c • volume := by
  rw [smoothDiffeomorphism_smul_measure_scale, smoothFlowHom_fixes_volume]

end InfoGeometry.Canonical.ArnoldInformationGeometry
