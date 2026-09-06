import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
import InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
import InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading

/-!
# Native `1 + 3 + 3 + 1` Peirce/operator grading bridge

This owner does not introduce a second decomposition of the canonical Zorn
carrier.  It names the four already-existing Peirce components as degree
`0,1,2,3`, reuses `ZornSpinor.zorn_peirce_decomposition`, and connects the
result to the repository-native exterior-coordinate and Cartan operator
grading owners.

The mathematical content is strictly algebraic:

* degree `0` is the upper diagonal Peirce component;
* degree `1` is the three-dimensional upper/color component;
* degree `2` is the three-dimensional lower/anticolor component;
* degree `3` is the lower diagonal Peirce component;
* diagonal coarse graining forgets exactly the degree `1` and `2` slots;
* for a genuine traceless Zorn derivation `axialCartanEnd k`, the associated
  left-regular operators carry weights `0,+kᵢ,-kᵢ,0`.

No identification with Standard-Model particle multiplets, spacetime fields,
or a Clifford/exterior algebra is asserted by this file.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge

open scoped BigOperators
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Lie.SplitOctonionPeirceDecompositionBridge
open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation

abbrev CZ := ZornMatrix ℝ

/-- Degree-zero scalar Peirce component. -/
def degreeZero (Z : CZ) : CZ :=
  peirceComponent zornPlus zornPlus Z

/-- Degree-one upper/vector Peirce component. -/
def degreeOne (Z : CZ) : CZ :=
  colorProject Z

/-- Degree-two lower/covector Peirce component. -/
def degreeTwo (Z : CZ) : CZ :=
  anticolorProject Z

/-- Degree-three lower scalar Peirce component. -/
def degreeThree (Z : CZ) : CZ :=
  peirceComponent zornMinus zornMinus Z

/-- The native Zorn decomposition is exactly the `1 + 3 + 3 + 1` Peirce
resolution. -/
theorem zorn_1331_decomposition (Z : CZ) :
    Z = degreeZero Z + degreeOne Z + degreeTwo Z + degreeThree Z := by
  simpa [degreeZero, degreeOne, degreeTwo, degreeThree] using
    (zorn_peirce_decomposition Z)

/-- Degree one is exactly the span readout in the three upper chiral basis
vectors. -/
theorem degreeOne_eq_chiralUpper_sum (Z : CZ) :
    degreeOne Z = ∑ i : Fin 3, Z.x i • chiralUpperBasis i := by
  simpa [degreeOne] using colorProject_eq_chiralUpper_sum Z

/-- Degree two is exactly the span readout in the three lower chiral basis
vectors. -/
theorem degreeTwo_eq_chiralLower_sum (Z : CZ) :
    degreeTwo Z = ∑ i : Fin 3, Z.y i • chiralLowerBasis i := by
  simpa [degreeTwo] using anticolorProject_eq_chiralLower_sum Z

/-- Degree zero contains only the upper diagonal coefficient. -/
theorem degreeZero_apply (Z : CZ) :
    degreeZero Z = { a := Z.a, b := 0, x := 0, y := 0 } := by
  simpa [degreeZero] using peirce_plus_plus_apply Z

/-- Degree three contains only the lower diagonal coefficient. -/
theorem degreeThree_apply (Z : CZ) :
    degreeThree Z = { a := 0, b := Z.b, x := 0, y := 0 } := by
  simpa [degreeThree] using peirce_minus_minus_apply Z

/-- The existing diagonal coarse-graining map retains precisely the degree-zero
and degree-three components. -/
theorem coarseGrain_eq_diagonal_degrees (Z : CZ) :
    coarseGrain Z = coarseGrain (degreeZero Z + degreeThree Z) := by
  rw [degreeZero_apply, degreeThree_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coarseGrain]

/-- The repository-native `Exterior3Coordinates` carrier has the same ordered
`1,3,3,1` coordinate packet.  This theorem is only a coordinate readout; it
does not identify the Zorn multiplication with the exterior product. -/
theorem exterior3_coordinate_packet
    (x : Exterior3Coordinates) :
    peirceExterior3Equiv x =
      ![x.1,
        x.2.1 0, x.2.1 1, x.2.1 2,
        x.2.2.2,
        x.2.2.1 0, x.2.2.1 1, x.2.2.1 2] := by
  rfl

/-- The four coordinate Peirce blocks resolve every `1+3+3+1` packet. -/
theorem peirce_coordinate_1331_resolution (x : PeirceCarrier) :
    proj11 x + proj10 x + proj01 x + proj00 x = x :=
  peirceExterior3_resolution x

/-- Operator-level Cartan grading of the four native Peirce sectors:
`0,+kᵢ,-kᵢ,0`.  This is an alias of the genuine derivation theorem, not a new
operator representation. -/
theorem cartan_operator_1331_packet
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (i : Fin 3) :
    ⁅axialCartanEnd k, leftRegular (zornPlus : CZ)⁆ = 0 ∧
    ⁅axialCartanEnd k, leftRegular (chiralUpperBasis i)⁆ =
      k i • leftRegular (chiralUpperBasis i) ∧
    ⁅axialCartanEnd k, leftRegular (chiralLowerBasis i)⁆ =
      (-k i) • leftRegular (chiralLowerBasis i) ∧
    ⁅axialCartanEnd k, leftRegular (zornMinus : CZ)⁆ = 0 :=
  axialCartan_chiral_operator_packet k hk i

end InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge
