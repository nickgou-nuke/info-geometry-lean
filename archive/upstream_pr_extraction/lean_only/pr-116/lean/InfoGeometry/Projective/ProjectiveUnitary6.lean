import InfoGeometry.Canonical.ProjectiveUnitary6

/-!
# Projective unitary six-state compatibility surface

The canonical owner of the concrete `PU(6)` construction is
`InfoGeometry.Canonical.ProjectiveUnitary6`.  This module preserves the
historical `InfoGeometry.Projective.ProjectiveUnitary6` import path without
duplicating definitions or proofs.
-/

namespace InfoGeometry.Projective.ProjectiveUnitary6

abbrev U6 := InfoGeometry.Canonical.ProjectiveUnitary6.U6
abbrev centerU6 : Subgroup U6 := InfoGeometry.Canonical.ProjectiveUnitary6.centerU6
abbrev PU6 := InfoGeometry.Canonical.ProjectiveUnitary6.PU6

abbrev toPU6 : U6 →* PU6 := InfoGeometry.Canonical.ProjectiveUnitary6.toPU6

theorem toPU6_z_eq_one (z : U6) (hz : z ∈ centerU6) : toPU6 z = 1 :=
  InfoGeometry.Canonical.ProjectiveUnitary6.toPU6_z_eq_one z hz

theorem projective_conjugation_relation
    (Theta T z : U6) (hz : z ∈ centerU6)
    (hpin : Theta * T * Theta⁻¹ = z * T⁻¹) :
    toPU6 Theta * toPU6 T * (toPU6 Theta)⁻¹ = (toPU6 T)⁻¹ :=
  InfoGeometry.Canonical.ProjectiveUnitary6.projective_conjugation_relation
    Theta T z hz hpin

end InfoGeometry.Projective.ProjectiveUnitary6
