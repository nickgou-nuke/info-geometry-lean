import InfoGeometry.Canonical.RicciMongeAmpere

namespace InfoGeometry.Topology

universe u

export InfoGeometry.Canonical.RicciMongeAmpere
  (RicciFlow IsRicciFixedPoint)

/-- Carrier for a connected-sum result.

The file does not construct a connected sum or state its universal property;
the previous declaration carried only an arbitrary result type. Keep that
scope explicit by using the native type carrier rather than a wrapper.
-/
abbrev ConnectedSum (M₁ M₂ : Type u) := Type u

abbrev ConnectedSum.ResultType
    {M₁ M₂ : Type u} (C : ConnectedSum M₁ M₂) : Type u := C

def ConnectedSum.mk
    {M₁ M₂ ResultType : Type u} : ConnectedSum M₁ M₂ := ResultType

end InfoGeometry.Topology
