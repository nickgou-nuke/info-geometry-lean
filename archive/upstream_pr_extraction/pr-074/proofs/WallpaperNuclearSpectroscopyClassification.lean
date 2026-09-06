import Mathlib
import proofs.GoutevTonevNuclearHamiltonian
import proofs.FixedLineRiemannKlein
import proofs.MirrorNucleiIsospinGNS

/-!
# Wallpaper nuclear spectroscopy classification

Finite classification layer for reading collective nuclear spectra through the
17 wallpaper groups of the holographic surface.

This file records the proposed spectroscopy dictionary as finite data:

* hexagonal wallpaper groups classify Elliott/SU(3)-style rotational bands;
* glide groups classify chiral doublet/Moebius partner bands;
* square/rectangular groups classify quadrupole-vibrational patterns;
* trigonal groups classify three-body/cluster patterns;
* mirror groups classify mirror-nucleus/isospin selection rules.

The physical identification of actual nuclei with fitted band data remains an
interpretive layer, not a claim that Lean has processed experimental spectra.
-/

noncomputable section

namespace WallpaperNuclearSpectroscopyClassification

/-- The 17 wallpaper groups in IUCr notation. -/
inductive WallpaperGroup17 where
  | p1 | p2 | pm | pg | cm | pmm | pmg | pgg | cmm
  | p4 | p4m | p4g | p3 | p3m1 | p31m | p6 | p6m
  deriving DecidableEq, Repr

/-- Explicit finite census of the wallpaper groups. -/
def allWallpaperGroups : List WallpaperGroup17 :=
  [.p1, .p2, .pm, .pg, .cm, .pmm, .pmg, .pgg, .cmm,
   .p4, .p4m, .p4g, .p3, .p3m1, .p31m, .p6, .p6m]

/-- The wallpaper census has 17 groups. -/
theorem allWallpaperGroups_length : allWallpaperGroups.length = 17 := rfl

/-- Nuclear spectroscopy clusters induced by wallpaper symmetry. -/
inductive NuclearSpectroscopyCluster where
  | primitiveTriaxial
  | mirrorIsospin
  | glideChiral
  | squareQuadrupole
  | trigonalCluster
  | hexagonalSU3Rotor
  deriving DecidableEq, Repr

/-- Extinction/selection-rule labels for the finite classification table. -/
inductive NuclearExtinctionRule where
  | noneAllTransitionsAllowed
  | isospinViolatingE1Extinguished
  | deltaJOneDoubletMixingExtinguished
  | nonSingletColorModeExtinguished
  | nonCountingOvertoneExtinguished
  | nonTriangularClusterModeExtinguished
  deriving DecidableEq, Repr

/-- Cluster assignment for each wallpaper group. -/
def nuclearCluster : WallpaperGroup17 → NuclearSpectroscopyCluster
  | .p1 | .p2 => .primitiveTriaxial
  | .pm | .cm | .cmm => .mirrorIsospin
  | .pg | .pmg | .pgg | .p4g => .glideChiral
  | .pmm | .p4 | .p4m => .squareQuadrupole
  | .p3 | .p3m1 | .p31m => .trigonalCluster
  | .p6 | .p6m => .hexagonalSU3Rotor

/-- Extinction/selection rule associated with each wallpaper group. -/
def extinctionRule : WallpaperGroup17 → NuclearExtinctionRule
  | .p1 | .p2 => .noneAllTransitionsAllowed
  | .pm | .cm | .cmm => .isospinViolatingE1Extinguished
  | .pg | .pmg | .pgg | .p4g => .deltaJOneDoubletMixingExtinguished
  | .pmm | .p4 | .p4m => .nonCountingOvertoneExtinguished
  | .p3 | .p3m1 | .p31m => .nonTriangularClusterModeExtinguished
  | .p6 | .p6m => .nonSingletColorModeExtinguished

/-- `p6m` is the hexagonal SU(3)-rotor class. -/
theorem p6m_cluster :
    nuclearCluster WallpaperGroup17.p6m = NuclearSpectroscopyCluster.hexagonalSU3Rotor := rfl

/-- `pg` is the glide/chiral-doublet class. -/
theorem pg_cluster :
    nuclearCluster WallpaperGroup17.pg = NuclearSpectroscopyCluster.glideChiral := rfl

/-- `p4m` is the quadrupole-vibrational class. -/
theorem p4m_cluster :
    nuclearCluster WallpaperGroup17.p4m = NuclearSpectroscopyCluster.squareQuadrupole := rfl

/-- `p3m1` is the trigonal/cluster class. -/
theorem p3m1_cluster :
    nuclearCluster WallpaperGroup17.p3m1 = NuclearSpectroscopyCluster.trigonalCluster := rfl

/-- `cm` is the mirror/isospin class. -/
theorem cm_cluster :
    nuclearCluster WallpaperGroup17.cm = NuclearSpectroscopyCluster.mirrorIsospin := rfl

/-- The glide rule extinguishes `Delta J = 1` doublet mixing. -/
theorem pg_extinction :
    extinctionRule WallpaperGroup17.pg =
      NuclearExtinctionRule.deltaJOneDoubletMixingExtinguished := rfl

/-- The hexagonal rule extinguishes non-singlet color modes. -/
theorem p6m_extinction :
    extinctionRule WallpaperGroup17.p6m =
      NuclearExtinctionRule.nonSingletColorModeExtinguished := rfl

/-- The mirror rule extinguishes isospin-violating E1 transitions. -/
theorem cm_extinction :
    extinctionRule WallpaperGroup17.cm =
      NuclearExtinctionRule.isospinViolatingE1Extinguished := rfl

end WallpaperNuclearSpectroscopyClassification

end noncomputable section
