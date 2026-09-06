import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge

/-!
# Native `1 + 3 + 3 + 1` exterior / Dirac--Souriau bridge

This owner closes two remaining compatibility edges without introducing a new
carrier or a second grading convention.

* The literal Mathlib exterior basis in
  `SplitOctonionExterior3HodgeDiracBridge` is already reindexed by the circular
  Peirce order.  We record its exact exterior degree packet
  `0,1,1,1,3,2,2,2`.
* The existing `toDiracSouriauSector` readout is shown to factor exactly through
  the four native Peirce degrees: its diagonal entries come from degrees `0`
  and `3`, while its off-diagonal pairings use only degrees `1` and `2`.

No multiplicative equivalence between the exterior algebra and split-octonion
Zorn multiplication is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge

abbrev CZ := ZornMatrix ℝ

/-- Exterior degree of the basis vector in the established circular Peirce
ordering. -/
def exteriorDegree1331 : Fin 8 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 2
  | 6 => 2
  | 7 => 2

/-- The degree labels are literally the cardinalities of the subsets indexing
the Mathlib exterior basis. -/
theorem exteriorDegree1331_eq_card_peirceSubset (i : Fin 8) :
    exteriorDegree1331 i = (peirceSubset i).card := by
  fin_cases i <;> native_decide

/-- The literal exterior basis and the circular Peirce basis agree under the
existing linear equivalence, with the same exact exterior degree label. -/
theorem exterior_basis_1331_packet (i : Fin 8) :
    exterior3CircularPeirceEquiv (exterior3PeirceBasis i) =
        circularPeirceBasis i ∧
      exteriorDegree1331 i = (peirceSubset i).card := by
  exact ⟨exterior3CircularPeirceEquiv_basis i,
    exteriorDegree1331_eq_card_peirceSubset i⟩

/-- The Dirac--Souriau `2 × 2` readout uses exactly the four Peirce degrees:
`0` and `3` on the diagonal, and only the `1`--`2` pairings off diagonal. -/
theorem toDiracSouriauSector_eq_1331_entries (z1 z2 : CZ) :
    toDiracSouriauSector z1 z2 =
      !![(degreeZero z1).a,
          dot (degreeOne z1).x (degreeTwo z2).y;
         dot (degreeTwo z1).y (degreeOne z2).x,
          (degreeThree z2).b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toDiracSouriauSector, degreeZero_apply, degreeThree_apply,
      degreeOne, degreeTwo, colorProject_apply, anticolorProject_apply]

/-- Equivalently, `toDiracSouriauSector` factors through the minimal degree
content needed for each of its two Zorn arguments. -/
theorem toDiracSouriauSector_factor_through_1331 (z1 z2 : CZ) :
    toDiracSouriauSector z1 z2 =
      toDiracSouriauSector
        (degreeZero z1 + degreeOne z1 + degreeTwo z1)
        (degreeOne z2 + degreeTwo z2 + degreeThree z2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toDiracSouriauSector, degreeZero_apply, degreeThree_apply,
      degreeOne, degreeTwo, colorProject_apply, anticolorProject_apply,
      dot]

/-- The diagonal coarse-graining and the Dirac--Souriau readout therefore
separate the same native four-degree packet in complementary ways. -/
theorem coarseGrain_and_diracSouriau_1331_packet (z1 z2 : CZ) :
    coarseGrain z1 = coarseGrain (degreeZero z1 + degreeThree z1) ∧
    toDiracSouriauSector z1 z2 =
      toDiracSouriauSector
        (degreeZero z1 + degreeOne z1 + degreeTwo z1)
        (degreeOne z2 + degreeTwo z2 + degreeThree z2) := by
  exact ⟨coarseGrain_eq_diagonal_degrees z1,
    toDiracSouriauSector_factor_through_1331 z1 z2⟩

end InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
