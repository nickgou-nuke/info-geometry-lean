/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldBeltramiVolume
import InfoGeometry.Canonical.SmoothDiffeomorphismDensityOrbit

/-!
# The physical Beltrami flow inside the smooth acting group

These four declarations retain their original fully qualified names in
`ArnoldInformationGeometry`. Their exact definitions and proofs are owned here
so dynamical symmetry consumers do not need the independent Fisher, matrix,
and KL aggregation imports. `ArnoldInformationGeometry` re-exports this owner.
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
