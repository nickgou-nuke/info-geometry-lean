import InfoGeometry.Topology.DelaunayFlipInterfaces
import InfoGeometry.Topology.PureBraidGroup

/-!
# Delaunay Pure Braid Representation Boundary

This file consumes the proven Delaunay quotient layer and exposes the final
boundary from an external pure-braid group model into Rohozhkin matrices. It
does not define `PB_n`, does not claim Markov invariance, and does not reopen
the local move proofs.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `rohozhkinPureBraidMatrix` evaluates any supplied boundary map through the
  proven Delaunay quotient matrix.
- `rohozhkin_respects_pure_braid_presentation` is the corresponding
  quotient/factorization readback theorem.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The file is conditional on an externally supplied group `PB` and map
`PB -> DelaunayQuotient moving`.

#### BUCKET 3: OPEN CLOSURE DEBT
- A completed pure-braid presentation for `rohozhkinTotalPoints moving`.
- A proof that the completed presentation maps into the Delaunay quotient.
- A group-homomorphism theorem into matrix units.
- Markov-move invariance.
-/

namespace InfoGeometry.Topology.RohozhkinBoundary

open InfoGeometry.Topology.Delaunay

/-- Total number of labeled points: `moving` moving points plus three fixed boundary points. -/
def rohozhkinTotalPoints (moving : ℕ) : ℕ :=
  moving + 3

/--
Boundary data from an externally formalized pure-braid group into the proven
Delaunay flip-word quotient.
-/
structure PureBraidRepresentationBoundary (moving : ℕ) (PB : Type) [Group PB] where
  totalPoints : ℕ := rohozhkinTotalPoints moving
  braidToQuotient : PB → DelaunayQuotient moving

/-- Matrix readout for an externally supplied pure-braid boundary map. -/
def rohozhkinPureBraidMatrix {moving : ℕ} {PB : Type} [Group PB]
    (boundary : PureBraidRepresentationBoundary moving PB) :
    PB → Matrix (Fin (rohozhkinDim moving)) (Fin (rohozhkinDim moving)) ℚ :=
  fun g => rohozhkinQuotientMatrix (boundary.braidToQuotient g)

/--
Quotient/factorization theorem for the boundary map.

This is not yet a group-homomorphism theorem; it only says that the matrix
readout factors through the already-proved Delaunay quotient.
-/
theorem rohozhkin_respects_pure_braid_presentation {moving : ℕ} {PB : Type} [Group PB]
    (boundary : PureBraidRepresentationBoundary moving PB) (g : PB) :
    rohozhkinPureBraidMatrix boundary g =
      rohozhkinQuotientMatrix (boundary.braidToQuotient g) :=
  rfl

end InfoGeometry.Topology.RohozhkinBoundary
