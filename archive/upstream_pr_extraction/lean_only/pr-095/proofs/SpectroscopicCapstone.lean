import proofs.ProjectiveWallpaperGaugePSA
import proofs.TrappedHarmonicModes
import proofs.NuclearSpectroscopyEnergyLevels
import proofs.NuclearWallpaperSpectraClassification
import proofs.ChiralConeAlgebraFinality
import proofs.BraidedCocycleWilsonEntropy
import proofs.ClebschGordanPenroseNonequilibriumSpinGraph

/-!
# Spectroscopic capstone

Final proved bundle for the wallpaper / trapped-mode / nuclear
spectroscopy / recoupling layers.

Finite/proved spine:
* 17 wallpaper groups;
* trapped harmonic modes and odd `pg` extinction;
* nuclear spectroscopy energy decomposition;
* wallpaper-to-nuclear spectral classification;
* finite Clebsch--Gordan/Penrose recoupling table.

-/

noncomputable section

namespace SpectroscopicCapstone

open ProjectiveWallpaperGaugePSA
open ClebschGordanPenroseNonequilibriumSpinGraph

/-- The capstone theorem: the finite wallpaper, trapped-mode, nuclear,
and recoupling layers compile together. -/
theorem spectroscopic_capstone_synthesis :
    ProjectiveWallpaperGaugePSA.allWallpaperGroups.length = 17 ∧
    TrappedHarmonicModes.primonOvertonePrimes.length = 3 ∧
    NuclearWallpaperSpectraClassification.hexagonalCluster.length = 2 ∧
    NuclearWallpaperSpectraClassification.glideCluster.length = 3 ∧
    NuclearWallpaperSpectraClassification.squareQuadrupoleCluster.length = 3 ∧
    NuclearWallpaperSpectraClassification.trigonalCluster.length = 2 ∧
    NuclearWallpaperSpectraClassification.nuclearSpectralClass
      WallpaperGroup.p6m =
        NuclearWallpaperSpectraClassification.NuclearSpectralClass.hexagonalSU3Rotor ∧
    NuclearWallpaperSpectraClassification.nuclearSpectralClass
      WallpaperGroup.pg =
        NuclearWallpaperSpectraClassification.NuclearSpectralClass.glideChiralDoublet ∧
    NuclearWallpaperSpectraClassification.nuclearSpectralClass
      WallpaperGroup.cm =
        NuclearWallpaperSpectraClassification.NuclearSpectralClass.mirrorIsospin ∧
    NuclearSpectroscopyEnergyLevels.deltaKHalf (1 / 2 : ℝ) = 1 ∧
    ChiralConeAlgebraFinality.NPlus + ChiralConeAlgebraFinality.NMinus =
      (1 : ChiralConeAlgebraFinality.M2C) ∧
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.j0 = true ∧
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.j1 = true ∧
    CGAllowed SpinLabel.jHalf SpinLabel.jHalf SpinLabel.jThreeHalf = false ∧
    regimeOfWilson (BraidedCocycleWilsonEntropy.triangleWilson
      BraidedCocycleWilsonEntropy.entropyCycle) =
        SpinGraphRegime.nonequilibriumAsymmetric := by
  constructor
  · exact ProjectiveWallpaperGaugePSA.allWallpaperGroups_length
  constructor
  · exact TrappedHarmonicModes.primon_overtone_count
  constructor
  · exact NuclearWallpaperSpectraClassification.hexagonal_cluster_length
  constructor
  · exact NuclearWallpaperSpectraClassification.glide_cluster_length
  constructor
  · exact NuclearWallpaperSpectraClassification.square_quadrupole_cluster_length
  constructor
  · exact NuclearWallpaperSpectraClassification.trigonal_cluster_length
  constructor
  · exact NuclearWallpaperSpectraClassification.p6m_is_hexagonal_su3_rotor
  constructor
  · exact NuclearWallpaperSpectraClassification.pg_is_glide_chiral_doublet
  constructor
  · exact NuclearWallpaperSpectraClassification.cm_is_mirror_isospin
  constructor
  · exact NuclearSpectroscopyEnergyLevels.deltaKHalf_half
  constructor
  · exact ChiralConeAlgebraFinality.chiral_projector_completeness
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · simp [regimeOfWilson]

end SpectroscopicCapstone

end noncomputable section
