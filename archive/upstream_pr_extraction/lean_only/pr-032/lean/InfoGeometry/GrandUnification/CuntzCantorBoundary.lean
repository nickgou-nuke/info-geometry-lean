import Mathlib.Algebra.Ring.Basic
import InfoGeometry.GrandUnification.HodgeCartanTrifactor

/-!
# TriFacet Projector Partition on the Cantor Boundary Readout

This module records the finite projector partition used as the boundary
readout of the thermodynamic model. It does not identify these scalar
projectors with Cuntz isometries: no operator star, range isometry, or Cuntz
representation is present in this carrier.

The proved statement is the finite algebraic partition
`P_plus + P_minus + P_zero = 1`. The genuine Cuntz relations for the binary
Cantor shift live in the native operator owner
`InfoGeometry.Topology.CantorBoundaryCuntzO2`.
-/

namespace InfoGeometry.GrandUnification.CuntzCantor

open InfoGeometry.GrandUnification.HodgeCartan
open InfoGeometry.Canonical.TrifactorDecomposition
open InfoGeometry.Canonical.TriFacetGeometry

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable (T : R)

/-- The exact TriFacet projector used by the boundary readout. -/
abbrev boundaryProjector_plus (T : R) : R := exact_op T

/-- The co-exact TriFacet projector used by the boundary readout. -/
abbrev boundaryProjector_minus (T : R) : R := coexact_op T

/-- The harmonic TriFacet projector used by the boundary readout. -/
abbrev boundaryProjector_zero (T : R) : R := harmonic_op T

/-- The three finite boundary projectors partition the unit. -/
theorem boundaryProjectors_sum_one :
    boundaryProjector_plus T + boundaryProjector_minus T +
        boundaryProjector_zero T = 1 := by
  unfold boundaryProjector_plus boundaryProjector_minus boundaryProjector_zero
  unfold exact_op coexact_op harmonic_op
  exact P_sum T

end InfoGeometry.GrandUnification.CuntzCantor
