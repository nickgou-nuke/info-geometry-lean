import InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge

/-!
# InfoGeometry.Canonical.SouriauWeylPartitionBridge

Canonical re-export of the thermodynamic Souriau/Weyl partition bridge.

This file exists so canonical-side imports can use the same name-space shape as
the rest of the canonical bridge layer without duplicating the underlying
implementation.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauWeylPartitionBridge

abbrev SouriauWeylPartitionBridge :=
  InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge.SouriauWeylPartitionBridge

end InfoGeometry.Canonical.SouriauWeylPartitionBridge
