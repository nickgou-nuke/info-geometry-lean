import InfoGeometry.Canonical.IntegralChiralCliffordOrder

/-!
# Topological readout of the integral chiral order

The carrier `M₂(ℤ)` has its native product topology.  Since the integer
coordinates are discrete, the parity order is a closed subset.  This is a
topological fact about the finite-coordinate model; it does not identify the
order with the full matrix ring or provide a scalar-extension theorem.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

theorem isClosed_integerChiralOrder :
    IsClosed (integerChiralOrder : Set M2Z) := by
  exact isClosed_discrete _

theorem isClosed_integralChiralCliffordOrder :
    IsClosed ({A : M2Z | integralChiralParity A} : Set M2Z) := by
  simpa [integralChiralParity] using isClosed_integerChiralOrder

end InfoGeometry.Topology
