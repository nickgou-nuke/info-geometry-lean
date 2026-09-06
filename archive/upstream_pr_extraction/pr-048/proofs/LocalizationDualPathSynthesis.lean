import InfoGeometry.External.Auto.BuresInformationGeodesicFlow
import proofs.StimulatedScatteringAmplituhedron

/-!
# Localization dual-path synthesis

This file combines both requested branches:

* the Bures/Fisher information-geodesic branch;
* the stimulated-scattering / amplituhedron gain-medium branch.

The imported branch lemmas supply the general statements. The concrete finite
equalities below are checked locally from the imported definitions.
-/

noncomputable section

namespace LocalizationDualPathSynthesis

/-- The imported Raman lane list has three entries by direct evaluation. -/
theorem local_raman_lane_count :
    StimulatedScatteringAmplituhedron.ramanLanes.length = 3 := by
  simp [StimulatedScatteringAmplituhedron.ramanLanes]

/-- The zero-occupation gain at unit input evaluates to one. -/
theorem local_stimulated_gain_unit :
    StimulatedScatteringAmplituhedron.stimulatedGain 1 0 = 1 := by
  norm_num [StimulatedScatteringAmplituhedron.stimulatedGain]

/-- The zero-parameter volume counter agrees with the Dikin counter. -/
theorem local_amplituhedron_zero_volume :
    StimulatedScatteringAmplituhedron.amplituhedronVolume 0 =
      StimulatedScatteringAmplituhedron.dikinVolumeCounter := by
  simp [StimulatedScatteringAmplituhedron.amplituhedronVolume,
    StimulatedScatteringAmplituhedron.dikinVolumeCounter]

/-- The four-wave count evaluates to four by arithmetic. -/
theorem local_four_wave_mixing_count :
    StimulatedScatteringAmplituhedron.fourWaveMixingCount = 4 := by
  norm_num [StimulatedScatteringAmplituhedron.fourWaveMixingCount]

/-- The dual-path theorem packages the finite conclusions from both branches. -/
theorem localization_dual_path_synthesis :
    (∀ K A, modularFlow K 0 A = A) ∧
    (∀ I θ E, 0 < I → θ * E ≤ fisherQuadratic I θ + dualFisherQuadratic I E) ∧
    (∀ I θ E, I ≠ 0 → deriv (fun x : ℝ => deriv (fisherQuadratic I) x) θ *
      deriv (fun x : ℝ => deriv (dualFisherQuadratic I) x) E = 1) ∧
    StimulatedScatteringAmplituhedron.ramanLanes.length = 3 ∧
    StimulatedScatteringAmplituhedron.stimulatedGain 1 0 = 1 ∧
    StimulatedScatteringAmplituhedron.amplituhedronVolume 0 =
      StimulatedScatteringAmplituhedron.dikinVolumeCounter ∧
    StimulatedScatteringAmplituhedron.fourWaveMixingCount = 4 := by
  refine And.intro ?modular ?afterModular
  · exact BuresInformationGeodesicFlow.modularFlow_zero_time
  · refine And.intro ?legendre ?afterLegendre
    · intro I θ E hI
      exact BuresInformationGeodesicFlow.fisher_legendre_geodesic_cost I θ E hI
    · refine And.intro ?curvature ?afterCurvature
      · intro I θ E hI
        exact BuresInformationGeodesicFlow.fisher_curvature_inverse I θ E hI
      · refine And.intro ?lanes ?afterLanes
        · exact local_raman_lane_count
        · refine And.intro ?gain ?afterGain
          · exact local_stimulated_gain_unit
          · refine And.intro ?volume ?mixing
            · exact local_amplituhedron_zero_volume
            · exact local_four_wave_mixing_count

end LocalizationDualPathSynthesis

end noncomputable section
