import InfoGeometry.Canonical.RicciMongeAmpere

namespace InfoGeometry.Topology

universe u

/--
A placeholder structure for Ricci Flow on a smooth manifold.
The Ricci-flow owner is the scale-dependent Ricci tensor family.
-/
abbrev RicciFlow (E : Type u) : Type _ :=
  InfoGeometry.Canonical.RicciMongeAmpere.RicciFlow E

abbrev IsRicciFixedPoint {E : Type u}
    (flow : RicciFlow E) : Prop :=
  InfoGeometry.Canonical.RicciMongeAmpere.IsRicciFixedPoint flow

/-- A placeholder structure for a Connected Sum of two manifolds. -/
structure ConnectedSum (M₁ M₂ : Type u) where
  /-- The resulting manifold type. -/
  ResultType : Type u

end InfoGeometry.Topology
