import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge

/-!
# Coadjoint Casimir Entropy

Abstract Casimir-entropy and symmetry-invariant geometry interfaces for the
canonical Souriau/coadjoint lane.

This file is an interface layer. It does not construct concrete coadjoint
actions or operator models.
-/

namespace InfoGeometry
namespace Canonical

/--
A functional is a generalized Casimir if it is constant along all symmetry or
coadjoint-flow directions.
-/
def IsGeneralizedCasimir
    {𝕜 State Obs : Type*}
    (S : State → 𝕜)
    (flow : Obs → State → State) : Prop :=
  ∀ X s, S (flow X s) = S s

/--
Response geometry is symmetry-invariant.
-/
def IsGeometryInvariant
    {𝕜 State Obs : Type*}
    (g : State → Obs → Obs → 𝕜)
    (flow : Obs → State → State) : Prop :=
  ∀ X A B s, g (flow X s) A B = g s A B

end Canonical
end InfoGeometry

