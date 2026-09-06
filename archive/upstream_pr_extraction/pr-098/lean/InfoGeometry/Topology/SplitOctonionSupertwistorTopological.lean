import InfoGeometry.Canonical.SplitOctonionSupertwistorBridge

/-!
# Topology of the finite Günaydin--Gürsey coordinate chart

The current canonical owner is an eight-coordinate structure over an
`ExteriorAlgebra`.  This file supplies the topology only after a topology on
that coefficient carrier is explicitly provided.  The topology on the
eight-coordinate structure is induced by its coordinate map; no projective or
supergeometric identification is inferred.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The eight coordinate readout of a Günaydin--Gürsey split basis. -/
def gunaydinGurseyCoordinates
    (Z : GunaydinGurseySplitBasis R V) :
    Fin 8 → ExteriorAlgebra R V :=
  ![Z.u0, Z.u1, Z.u2, Z.u3, Z.u0s, Z.u1s, Z.u2s, Z.u3s]

section Topological

variable [TopologicalSpace (ExteriorAlgebra R V)]

/-- The chart topology induced by all eight coefficient coordinates. -/
instance : TopologicalSpace (GunaydinGurseySplitBasis R V) :=
  TopologicalSpace.induced gunaydinGurseyCoordinates inferInstance

theorem continuous_gunaydinGurseyCoordinate (i : Fin 8) :
    Continuous (fun Z : GunaydinGurseySplitBasis R V =>
      gunaydinGurseyCoordinates Z i) := by
  exact (continuous_apply i).comp continuous_induced_dom

theorem continuous_levelZeroOctonionicAction_coordinate
    (a : ExteriorAlgebra R V) (i : Fin 8)
    (hleft : Continuous (fun x : ExteriorAlgebra R V => a * x)) :
    Continuous (fun Z : GunaydinGurseySplitBasis R V =>
      gunaydinGurseyCoordinates (levelZeroOctonionicAction a Z) i) := by
  have h := hleft.comp (continuous_gunaydinGurseyCoordinate
    (R := R) (V := V) i)
  fin_cases i <;>
    simpa [Function.comp_def, gunaydinGurseyCoordinates,
      levelZeroOctonionicAction] using h

variable [T1Space (ExteriorAlgebra R V)]

/-- A prescribed coordinate value is a closed subset of the induced chart. -/
def gunaydinGurseyCoordinateLevelSet
    (i : Fin 8) (a : ExteriorAlgebra R V) :
    Set (GunaydinGurseySplitBasis R V) :=
  {Z | gunaydinGurseyCoordinates Z i = a}

theorem isClosed_gunaydinGurseyCoordinateLevelSet
    (i : Fin 8) (a : ExteriorAlgebra R V) :
    IsClosed (gunaydinGurseyCoordinateLevelSet (R := R) (V := V) i a) := by
  change IsClosed ((fun Z : GunaydinGurseySplitBasis R V =>
    gunaydinGurseyCoordinates Z i) ⁻¹' ({a} : Set (ExteriorAlgebra R V)))
  exact isClosed_singleton.preimage (continuous_gunaydinGurseyCoordinate i)

end Topological

end InfoGeometry.Topology
