import proofs.NuclearSpectroscopyEnergyLevels

/-!
# Nuclear spectra by wallpaper group

The 17 wallpaper groups are used as finite spectroscopic labels for collective
nuclear-motion regimes.  The classification table and selection rules below are
finite bookkeeping for the named clusters and forbidden transitions.
-/

noncomputable section

namespace NuclearWallpaperSpectraClassification

abbrev WallpaperGroup := ProjectiveWallpaperGaugePSA.WallpaperGroup

/-- Coarse nuclear-spectroscopy classes induced by wallpaper symmetry. -/
inductive NuclearSpectralClass where
  | genericTriaxial
  | mirrorIsospin
  | glideChiralDoublet
  | squareQuadrupole
  | trigonalCluster
  | hexagonalSU3Rotor
  deriving DecidableEq, Repr

/-- Spectroscopic transition channels used in the extinction table. -/
inductive NuclearTransition where
  | arbitrary
  | deltaJOneDoubletMixing
  | nonsingletColorMode
  | isospinViolatingE1
  deriving DecidableEq, Repr

open ProjectiveWallpaperGaugePSA

/-- Wallpaper-group classification of collective nuclear spectra. -/
def nuclearSpectralClass : WallpaperGroup → NuclearSpectralClass
  | .p1 | .p2 | .pm | .cmm | .p4g | .p31m => .genericTriaxial
  | .cm => .mirrorIsospin
  | .pg | .pmg | .pgg => .glideChiralDoublet
  | .pmm | .p4 | .p4m => .squareQuadrupole
  | .p3 | .p3m1 => .trigonalCluster
  | .p6 | .p6m => .hexagonalSU3Rotor

/-- The finite extinction/selection rule associated to each wallpaper group. -/
def forbiddenTransition : WallpaperGroup → Option NuclearTransition
  | .pg | .pmg | .pgg => some .deltaJOneDoubletMixing
  | .p6 | .p6m => some .nonsingletColorMode
  | .cm => some .isospinViolatingE1
  | _ => none

/-- Boolean visibility of a transition in a wallpaper nuclear class. -/
def transitionAllowed (G : WallpaperGroup) (T : NuclearTransition) : Bool :=
  forbiddenTransition G != some T

/-- The groups named in the hexagonal/SU(3) nuclear shell cluster. -/
def hexagonalCluster : List WallpaperGroup := [.p6, .p6m]

/-- The groups named in the glide/chiral-doublet cluster. -/
def glideCluster : List WallpaperGroup := [.pg, .pmg, .pgg]

/-- The square/rectangular quadrupole-vibration cluster. -/
def squareQuadrupoleCluster : List WallpaperGroup := [.pmm, .p4, .p4m]

/-- The trigonal three-body/cluster-motion cluster. -/
def trigonalCluster : List WallpaperGroup := [.p3, .p3m1]

@[simp] theorem hexagonal_cluster_length : hexagonalCluster.length = 2 := rfl
@[simp] theorem glide_cluster_length : glideCluster.length = 3 := rfl
@[simp] theorem square_quadrupole_cluster_length : squareQuadrupoleCluster.length = 3 := rfl
@[simp] theorem trigonal_cluster_length : trigonalCluster.length = 2 := rfl

@[simp] theorem p6m_is_hexagonal_su3_rotor :
    nuclearSpectralClass WallpaperGroup.p6m = NuclearSpectralClass.hexagonalSU3Rotor := rfl

@[simp] theorem p6_is_hexagonal_su3_rotor :
    nuclearSpectralClass WallpaperGroup.p6 = NuclearSpectralClass.hexagonalSU3Rotor := rfl

@[simp] theorem pg_is_glide_chiral_doublet :
    nuclearSpectralClass WallpaperGroup.pg = NuclearSpectralClass.glideChiralDoublet := rfl

@[simp] theorem pmg_is_glide_chiral_doublet :
    nuclearSpectralClass WallpaperGroup.pmg = NuclearSpectralClass.glideChiralDoublet := rfl

@[simp] theorem pgg_is_glide_chiral_doublet :
    nuclearSpectralClass WallpaperGroup.pgg = NuclearSpectralClass.glideChiralDoublet := rfl

@[simp] theorem cm_is_mirror_isospin :
    nuclearSpectralClass WallpaperGroup.cm = NuclearSpectralClass.mirrorIsospin := rfl

@[simp] theorem pg_forbids_deltaJ_one_doublet_mixing :
    transitionAllowed WallpaperGroup.pg NuclearTransition.deltaJOneDoubletMixing = false := rfl

@[simp] theorem p6m_forbids_nonsinglet_color_modes :
    transitionAllowed WallpaperGroup.p6m NuclearTransition.nonsingletColorMode = false := rfl

@[simp] theorem cm_forbids_isospin_violating_E1 :
    transitionAllowed WallpaperGroup.cm NuclearTransition.isospinViolatingE1 = false := rfl

@[simp] theorem p1_allows_deltaJ_one_doublet_mixing :
    transitionAllowed WallpaperGroup.p1 NuclearTransition.deltaJOneDoubletMixing = true := rfl

/-- Capstone synthesis: the classification and extinction table compile. -/
theorem nuclear_wallpaper_spectra_classification_synthesis :
    ProjectiveWallpaperGaugePSA.allWallpaperGroups.length = 17 ∧
    hexagonalCluster.length = 2 ∧
    glideCluster.length = 3 ∧
    squareQuadrupoleCluster.length = 3 ∧
    trigonalCluster.length = 2 ∧
    nuclearSpectralClass WallpaperGroup.p6m = NuclearSpectralClass.hexagonalSU3Rotor ∧
    nuclearSpectralClass WallpaperGroup.pg = NuclearSpectralClass.glideChiralDoublet ∧
    nuclearSpectralClass WallpaperGroup.cm = NuclearSpectralClass.mirrorIsospin ∧
    transitionAllowed WallpaperGroup.pg NuclearTransition.deltaJOneDoubletMixing = false ∧
    transitionAllowed WallpaperGroup.p6m NuclearTransition.nonsingletColorMode = false ∧
    transitionAllowed WallpaperGroup.cm NuclearTransition.isospinViolatingE1 = false ∧
    TrappedHarmonicModes.primonOvertonePrimes.length = 3 := by
  constructor
  · exact ProjectiveWallpaperGaugePSA.allWallpaperGroups_length
  constructor
  · exact hexagonal_cluster_length
  constructor
  · exact glide_cluster_length
  constructor
  · exact square_quadrupole_cluster_length
  constructor
  · exact trigonal_cluster_length
  constructor
  · exact p6m_is_hexagonal_su3_rotor
  constructor
  · exact pg_is_glide_chiral_doublet
  constructor
  · exact cm_is_mirror_isospin
  constructor
  · exact pg_forbids_deltaJ_one_doublet_mixing
  constructor
  · exact p6m_forbids_nonsinglet_color_modes
  constructor
  · exact cm_forbids_isospin_violating_E1
  · exact TrappedHarmonicModes.primon_overtone_count

end NuclearWallpaperSpectraClassification

end noncomputable section
