import proofs.PrimonCuntzTower
import proofs.TorusKleinO55Bridge
import proofs.PhaseConjugateVacuumMirror
import proofs.VacuumJonesKleinBirefringence
import proofs.TopologicalAndreevPump
import proofs.BuresFisherAndreevGeodesicFlow

/-!
# Metamaterial quasicrystal Bloch synthesis

Finite theorem-honest structural capstone for the quasicrystal/metamaterial
reading:

* the Cantor/primon lattice is represented by finite prime samples and the
  existing finite Cuntz-tower embedding/Dirac compatibility;
* Klein--Bloch twisting is represented by the Klein glide relation and the
  orientation-reversing generator sign;
* the active metasurface is represented by the phase-conjugate/Andreev mirror
  and `p6m` wallpaper selection counts;
* Raman visibility is represented by the existing optical trivial-sector
  selection theorem.
-/

noncomputable section

namespace MetamaterialQuasicrystalBloch

/-- First three prime spacings used as finite quasicrystal samples. -/
def primeSamples : List ℕ := [2, 3, 5]

@[simp] theorem prime_sample_count : primeSamples.length = 3 := rfl

/-- Finite long-range-order proxy: ordered adjacent samples. -/
def OrderedPrimeSamples : Prop := 2 < 3 ∧ 3 < 5

@[simp] theorem ordered_prime_samples : OrderedPrimeSamples := by
  constructor <;> norm_num

/-- Finite non-periodicity proxy: adjacent spacings are not all equal. -/
def NonPeriodicPrimeSpacings : Prop := 3 - 2 ≠ 5 - 3

@[simp] theorem nonperiodic_prime_spacings : NonPeriodicPrimeSpacings := by
  norm_num [NonPeriodicPrimeSpacings]

/-- Klein--Bloch mode label: ordinary Bloch momentum plus chirality. -/
structure KleinBlochMode where
  momentum : ℤ
  chirality : TorusKleinO55Bridge.ManifoldGenerator

/-- The Klein glide flips the finite chirality label. -/
def kleinBlochTwist (m : KleinBlochMode) : KleinBlochMode :=
  { momentum := -m.momentum,
    chirality := TorusKleinO55Bridge.ManifoldGenerator.kleinGlide }

@[simp] theorem kleinBlochTwist_momentum (m : KleinBlochMode) :
    (kleinBlochTwist m).momentum = -m.momentum := rfl

@[simp] theorem kleinBlochTwist_orientation_reversing (m : KleinBlochMode) :
    TorusKleinO55Bridge.generatorOrientationSign (kleinBlochTwist m).chirality = -1 := rfl

/-- The finite Cuntz tower supplies an isometric ordered cylinder step. -/
theorem primon_cuntz_isometric_step (n : ℕ)
    (f : InfoGeometry.Quantum.PrimonCuntzTower.Stage n) :
    ‖InfoGeometry.Quantum.PrimonCuntzTower.embFun n f‖ = ‖f‖ :=
  InfoGeometry.Quantum.PrimonCuntzTower.emb_isometry n f

/-- Finite quasicrystal arithmetic: ordered but non-periodic prime samples. -/
theorem finite_quasicrystal_prime_arithmetic :
    primeSamples.length = 3 ∧ OrderedPrimeSamples ∧ NonPeriodicPrimeSpacings := by
  constructor
  · exact prime_sample_count
  · constructor
    · exact ordered_prime_samples
    · exact nonperiodic_prime_spacings

/-- The finite Klein--Bloch twist packages momentum inversion with the existing
orientation-reversing Klein generator. -/
theorem klein_bloch_twist_kernel (m : KleinBlochMode) :
    (kleinBlochTwist m).momentum = -m.momentum ∧
    TorusKleinO55Bridge.generatorOrientationSign (kleinBlochTwist m).chirality = -1 ∧
    O55CartanPhononReduction.o55CartanRank = 5 ∧
    TorusKleinO55Bridge.doubledCartanCarrierDimension = 10 := by
  constructor
  · exact kleinBlochTwist_momentum m
  · constructor
    · exact kleinBlochTwist_orientation_reversing m
    · constructor
      · exact O55CartanPhononReduction.o55_cartan_rank_eq
      · exact TorusKleinO55Bridge.doubled_cartan_carrier_dimension_eq

/-- Capstone package: finite metamaterial/quasicrystal/Bloch bookkeeping compiles. -/
theorem metamaterial_quasicrystal_bloch_finite_package
    (m : KleinBlochMode) (gain loss : ℝ) :
    primeSamples.length = 3 ∧
    OrderedPrimeSamples ∧
    NonPeriodicPrimeSpacings ∧
    (kleinBlochTwist m).momentum = -m.momentum ∧
    TorusKleinO55Bridge.generatorOrientationSign (kleinBlochTwist m).chirality = -1 ∧
    (∀ z : ℂ, G (T z) = T_inv (G z)) ∧
    (∀ z : ℂ, G (G z) = z + 2) ∧
    O55CartanPhononReduction.o55CartanRank = 5 ∧
    TorusKleinO55Bridge.doubledCartanCarrierDimension = 10 ∧
    O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 ∧
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
        O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 ∧
    VacuumJonesKleinBirefringence.OpticalRamanActive
      VacuumJonesKleinBirefringence.OpticalS3Sector.trivial ∧
    TopologicalAndreevPump.generationPhases.length = 3 ∧
    (0 < TopologicalAndreevPump.gainMinusLoss gain loss ↔ loss < gain) ∧
    StimulatedScatteringAmplituhedron.fourWaveMixingCount = 4 := by
  rcases finite_quasicrystal_prime_arithmetic with ⟨hlen, hordered, hnonperiodic⟩
  rcases klein_bloch_twist_kernel m with ⟨hmomentum, horientation, hrank, hdim⟩
  have hglide : ∀ z : ℂ, G (T z) = T_inv (G z) := fun z =>
    TorusKleinO55Bridge.klein_glide_twists_torus_translation z
  have hsquare : ∀ z : ℂ, G (G z) = z + 2 := fun z =>
    TorusKleinO55Bridge.klein_glide_square_is_translation z
  have hactive_rank : O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 :=
    O55GradedGeneratorBasis.active_graded_generator_count_eq
  have hp6m :
      ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
        ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
          O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 :=
    WallpaperO55FrozenSelectionBridge.p6m_psa_count_matches_active_o55_plus_base
  have hraman :
      VacuumJonesKleinBirefringence.OpticalRamanActive
        VacuumJonesKleinBirefringence.OpticalS3Sector.trivial :=
    PhaseConjugateVacuumMirror.wallpaper_slm_trivial_sector
  have hphases : TopologicalAndreevPump.generationPhases.length = 3 :=
    TopologicalAndreevPump.generation_phase_count
  have hgain :
      0 < TopologicalAndreevPump.gainMinusLoss gain loss ↔ loss < gain :=
    TopologicalAndreevPump.gain_overcomes_loss_iff_positive_margin gain loss
  have hmix : StimulatedScatteringAmplituhedron.fourWaveMixingCount = 4 :=
    StimulatedScatteringAmplituhedron.four_wave_mixing_count_eq_four
  exact ⟨hlen, hordered, hnonperiodic, hmomentum, horientation, hglide, hsquare,
    hrank, hdim, hactive_rank, hp6m, hraman, hphases, hgain, hmix⟩

#check metamaterial_quasicrystal_bloch_finite_package

end MetamaterialQuasicrystalBloch

end noncomputable section
