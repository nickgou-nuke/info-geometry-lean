import Mathlib
import InfoGeometry.Canonical.SplitPauliMatrixRelations
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

namespace InfoGeometry.Canonical

/-!
# Finite sector bookkeeping for the supertwistor carrier

`SplitOctonionSupertwistorBridge` owns the actual carrier. This file records only the
finite coordinate partition of its eight basis labels into one two-slot pair
and three two-slot pairs.  It does not define a Clifford action on the carrier,
identify it with projective supertwistor space, or prove a split-octonion
factorization of that action.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

abbrev CartanPairCoordinates (K : Type*) := Fin 2 → K
abbrev ChiralPairCoordinates (K : Type*) := Fin 2 → K
abbrev ThreeChiralCoordinates (K : Type*) := Fin 3 → ChiralPairCoordinates K

/-- A coordinate packet with one two-slot pair and three labelled two-slot pairs. -/
abbrev SupertwistorSectorCoordinates (K : Type*) :=
  CartanPairCoordinates K × ThreeChiralCoordinates K

/-- The finite slot count of the coordinate packet. -/
theorem supertwistor_sector_slot_count :
    Fintype.card (Fin 2) + Fintype.card (Fin 3) * Fintype.card (Fin 2) = 8 := by
  decide

/-- The existing split-octonion basis has the same eight labels. -/
theorem splitOctonionBasis_slot_count :
    Fintype.card Basis8 = 8 := by
  decide

/-- A theorem-safe coordinate packet for the existing supertwistor carrier. -/
structure SupertwistorCliffordDecomposition (K : Type*) [CommRing K] where
  cartan : CartanPairCoordinates K
  chiral : ThreeChiralCoordinates K

/-- The decomposition is only a coordinate projection, not an algebra action. -/
def SupertwistorCliffordDecomposition.cartanCoordinates
    {K : Type*} [CommRing K]
    (D : SupertwistorCliffordDecomposition K) : CartanPairCoordinates K :=
  D.cartan

def SupertwistorCliffordDecomposition.chiralCoordinates
    {K : Type*} [CommRing K]
    (D : SupertwistorCliffordDecomposition K) : ThreeChiralCoordinates K :=
  D.chiral

theorem supertwistor_clifford_coordinate_count :
    Fintype.card (Fin 2) + Fintype.card (Fin 3) * Fintype.card (Fin 2) =
      Fintype.card Basis8 := by
  rw [supertwistor_sector_slot_count, splitOctonionBasis_slot_count]

end InfoGeometry.Canonical
