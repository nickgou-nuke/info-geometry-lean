import proofs.SuperconductingHolographicResonator
import proofs.MetamaterialQuasicrystalBloch
import proofs.GaugeLnQTensorNetworkToy

/-!
# Topological metasurface supercurrent

Finite theorem-honest synthesis for the patterned photonic/topological
metasurface reading:

* `p6m` wallpaper selection supplies the finite lithographic mask count;
* quasicrystal order is represented by the `[2,3,5]` prime sample arithmetic;
* swirling supercurrents are represented by finite Wilson circulation;
* standing-wave coherence is represented by the resonator zero-time overlap and
  phase-locked generation count;
-/

noncomputable section

namespace TopologicalMetasurfaceSupercurrent

/-- Finite swirl orientation around a wallpaper cell. -/
inductive SwirlDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Reverse the finite swirl direction. -/
def reverseSwirl : SwirlDirection → SwirlDirection
  | .clockwise => .counterclockwise
  | .counterclockwise => .clockwise

@[simp] theorem reverseSwirl_involutive (s : SwirlDirection) :
    reverseSwirl (reverseSwirl s) = s := by
  cases s <;> rfl

/-- Quantized swirl count in the finite Wilson triangle. -/
def quantizedSwirlCount : ℤ :=
  BraidedCocycleWilsonEntropy.triangleWilson
    BraidedCocycleWilsonEntropy.entropyCycle

@[simp] theorem quantized_swirl_count_eq_three :
    quantizedSwirlCount = 3 := rfl

/-- Finite photonic bandgap toy: an electron/positron pair threshold. -/
def photonicBandgapToy (electronMass : ℝ) : ℝ := 2 * electronMass

@[simp] theorem photonicBandgapToy_eq_pair_threshold (m : ℝ) :
    photonicBandgapToy m = 2 * m := rfl



/-- Finite wallpaper/metasurface kernel: active `O(5,5)` plus scalar base matches
`p6m`, and the Wilson swirl has count `3`. -/
theorem finite_metasurface_swirl_kernel :
    O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 ∧
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
        O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 ∧
    quantizedSwirlCount = 3 ∧
    MetamaterialQuasicrystalBloch.primeSamples.length = 3 ∧
    MetamaterialQuasicrystalBloch.NonPeriodicPrimeSpacings := by
  constructor
  · exact O55GradedGeneratorBasis.active_graded_generator_count_eq
  constructor
  · exact WallpaperO55FrozenSelectionBridge.p6m_psa_count_matches_active_o55_plus_base
  constructor
  · rfl
  constructor
  · exact MetamaterialQuasicrystalBloch.prime_sample_count
  · exact MetamaterialQuasicrystalBloch.nonperiodic_prime_spacings

/-- Capstone: finite topological metasurface/supercurrent bookkeeping compiles. -/
theorem topological_metasurface_supercurrent_synthesis
    (electronMass gain loss K : ℝ) (A : ℂ) :
    reverseSwirl (reverseSwirl SwirlDirection.clockwise) = SwirlDirection.clockwise ∧
    quantizedSwirlCount = 3 ∧
    BraidedCocycleWilsonEntropy.BrokenDetailedBalance
      BraidedCocycleWilsonEntropy.entropyCycle ∧
    MetamaterialQuasicrystalBloch.primeSamples.length = 3 ∧
    MetamaterialQuasicrystalBloch.OrderedPrimeSamples ∧
    MetamaterialQuasicrystalBloch.NonPeriodicPrimeSpacings ∧
    O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 ∧
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
        O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 ∧
    VacuumJonesKleinBirefringence.OpticalRamanActive
      VacuumJonesKleinBirefringence.OpticalS3Sector.trivial ∧
    modularFlow K 0 A = A ∧
    TopologicalAndreevPump.generationPhases.length = 3 ∧
    (0 < TopologicalAndreevPump.gainMinusLoss gain loss ↔ loss < gain) ∧
    StimulatedScatteringAmplituhedron.fourWaveMixingCount = 4 ∧
    photonicBandgapToy electronMass = 2 * electronMass := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact BraidedCocycleWilsonEntropy.entropyCycle_breaks_detailedBalance
  constructor
  · exact MetamaterialQuasicrystalBloch.prime_sample_count
  constructor
  · exact MetamaterialQuasicrystalBloch.ordered_prime_samples
  constructor
  · exact MetamaterialQuasicrystalBloch.nonperiodic_prime_spacings
  constructor
  · exact O55GradedGeneratorBasis.active_graded_generator_count_eq
  constructor
  · exact WallpaperO55FrozenSelectionBridge.p6m_psa_count_matches_active_o55_plus_base
  constructor
  · exact PhaseConjugateVacuumMirror.wallpaper_slm_trivial_sector
  constructor
  · exact BuresInformationGeodesicFlow.modularFlow_zero_time K A
  constructor
  · exact TopologicalAndreevPump.generation_phase_count
  constructor
  · exact TopologicalAndreevPump.gain_overcomes_loss_iff_positive_margin gain loss
  constructor
  · exact StimulatedScatteringAmplituhedron.four_wave_mixing_count_eq_four
  · rfl

#check topological_metasurface_supercurrent_synthesis

end TopologicalMetasurfaceSupercurrent

end noncomputable section
