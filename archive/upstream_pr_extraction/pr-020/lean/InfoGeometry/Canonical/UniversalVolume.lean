import InfoGeometry.Volume.LogPotential
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Volume.DeterminantBundle

/-!
# Universal Volume Umbrella

Umbrella module for the multi-layered volume theory.
Fuses determinants, log-potentials, RN derivatives, and Connes cocycles.
-/

namespace InfoGeometry.Canonical.UniversalVolume

export InfoGeometry.Volume.LogPotential (LogAbsVolume logAbsVolume_add)
export InfoGeometry.Volume.ConnesCocycle (IsConnesCocycle cocycle_additive_potential)
export InfoGeometry.Volume.DeterminantBundle (DeterminantLine weylAction Dilation)

end InfoGeometry.Canonical.UniversalVolume
