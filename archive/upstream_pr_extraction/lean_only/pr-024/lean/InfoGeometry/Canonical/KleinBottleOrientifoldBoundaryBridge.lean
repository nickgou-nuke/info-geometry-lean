import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.KleinBottleTopology
import InfoGeometry.Canonical.KleinBottleOrientifold
import InfoGeometry.Canonical.CantorSimplicialHomotopy

/-!
# InfoGeometry.Canonical.KleinBottleOrientifoldBoundaryBridge

Bridge from the existing orientifold hypothesis packet to the matrix-level Klein
boundary operator used by `KleinBottleTopology`.

This file is intentionally modest:

- the orientifold packet remains hypothesis data;
- the boundary operator is supplied explicitly;
- the conclusion is only trace closure for finite boundary operators, and the
  corresponding closure for the existing Cantor simplicial packet.

It does **not** prove that the orientifold packet is geometrically realized, nor
that any number-theoretic or string-theoretic theory follows from it.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `orientifold_packet_trace_closed`
- `orientifold_packet_closes_cantor_boundary_faces`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- both theorems depend on an explicit `OrientifoldPrimeGasPacket` and an
  explicit orthogonal parity operator.

#### BUCKET 3: OPEN CLOSURE DEBT
No global orientifold realization, no physical anomaly cancellation theorem, and
no Katz-Sarnak / string-spectrum statement are proved here.
-/

namespace InfoGeometry.Canonical.KleinBottleOrientifoldBoundaryBridge

open Matrix
open InfoGeometry.Canonical.KleinBottleTopology
open InfoGeometry.Canonical.KleinBottleOrientifold
open InfoGeometry.Canonical.CantorSimplicialHomotopy
open InfoGeometry.Canonical.PrimeGasMaxEnt

/--
Existing orientifold hypothesis packet plus the explicit parity operator needed
by the matrix-level Klein gluing theorem.
-/
structure OrientifoldBoundaryOperatorPacket (D : PrimeGasJaynesData) where
  orientifoldPacket : OrientifoldPrimeGasPacket D
  parityOperator : Matrix (Fin 32) (Fin 32) ℝ
  parityOperator_orthogonal : parityOperatorᵀ * parityOperator = 1

/--
If a boundary operator has zero trace, then the Klein gluing induced by the
packet's parity operator preserves that zero trace.
-/
theorem orientifold_packet_trace_closed
    {D : PrimeGasJaynesData}
    (B : OrientifoldBoundaryOperatorPacket D)
    (M : Matrix (Fin 32) (Fin 32) ℝ)
    (h_trace : Matrix.trace M = 0) :
    Matrix.trace (klein_gluing M B.parityOperator) = 0 := by
  exact klein_topology_trace_closure M B.parityOperator B.parityOperator_orthogonal h_trace

/--
The same bridge closes every boundary face of the existing Cantor simplicial
packet, provided the packet already carries the `chiral_balance` trace witness.
-/
theorem orientifold_packet_closes_cantor_boundary_faces
    {D : PrimeGasJaynesData}
    (B : OrientifoldBoundaryOperatorPacket D)
    (n : ℕ)
    (step : KanSimplicialStep n) :
    ∀ i, Matrix.trace (klein_gluing (step.boundary_face i) B.parityOperator) = 0 := by
  intro i
  exact orientifold_packet_trace_closed B (step.boundary_face i) (step.chiral_balance i)

end InfoGeometry.Canonical.KleinBottleOrientifoldBoundaryBridge
