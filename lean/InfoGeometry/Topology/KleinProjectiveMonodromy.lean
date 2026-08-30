import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Projective.ProjectiveUnitary6

/-!
# Projective Klein monodromy compatibility surface

The canonical owners of the presented Klein group and its projective
representation live in `InfoGeometry.Canonical.KleinPresentedGroup` and
`InfoGeometry.Canonical.ProjectiveUnitary6`.  This module keeps the historical
topology-facing names without rebuilding either construction.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Projective
open InfoGeometry.Projective.ProjectiveUnitary6
open InfoGeometry.Canonical.KleinPresentedGroup

abbrev KleinGroup := InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup
abbrev a : KleinGroup := toKlein genA
abbrev b : KleinGroup := toKlein genB
abbrev kleinRelator := InfoGeometry.Canonical.KleinPresentedGroup.kleinRelator

structure KleinMonodromyData where
  Θ : U6
  T : U6
  z : U6
  hz : z ∈ centerU6
  hpin : (Θ : Matrix (Fin 6) (Fin 6) ℂ) * (T : Matrix (Fin 6) (Fin 6) ℂ) *
      star (Θ : Matrix (Fin 6) (Fin 6) ℂ) =
      (z : Matrix (Fin 6) (Fin 6) ℂ) * star (T : Matrix (Fin 6) (Fin 6) ℂ)

theorem projective_klein_relation {data : KleinMonodromyData} :
    toPU6 data.Θ * toPU6 data.T * (toPU6 data.Θ)⁻¹ =
      (toPU6 data.T)⁻¹ := by
  apply InfoGeometry.Canonical.ProjectiveUnitary6.projective_conjugation_relation
    data.Θ data.T data.z data.hz
  apply Subtype.ext
  simpa [Matrix.mul_assoc] using data.hpin

def kleinProjectiveRep {data : KleinMonodromyData} : KleinGroup →* PU6 :=
  InfoGeometry.Canonical.KleinPresentedGroup.kleinProjectiveRep
    data.Θ data.T data.z data.hz (by
      apply Subtype.ext
      simpa [Matrix.mul_assoc] using data.hpin)

end InfoGeometry.Topology
