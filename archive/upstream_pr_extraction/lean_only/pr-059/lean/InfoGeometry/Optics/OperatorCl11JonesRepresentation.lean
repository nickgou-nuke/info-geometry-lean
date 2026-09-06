import InfoGeometry.Canonical.OperatorCl11WittBasis
import InfoGeometry.Optics.OperatorValuedCliffordJones

/-!
# The operator-valued Jones representation of the `Cl(1,1)` packet

The entries of the matrices below are elements of an arbitrary operator ring
`B`.  This theorem therefore instantiates the abstract noncommutative Witt
packet without reducing its coefficients to scalars or diagonal entries.
-/

namespace InfoGeometry.Optics.OperatorCl11JonesRepresentation

open InfoGeometry.Clifford
open InfoGeometry.Optics.OperatorValuedCliffordJones
open InfoGeometry.Canonical.OperatorCl11WittBasis

variable {B : Type*} [Ring B] [Algebra ℂ B] [Algebra ℚ B]

instance representedOperatorCl11 :
    OperatorCl11 (sheetGamma (B := B)) (sheetJ (B := B)) where
  gamma_sq := by
    simpa only [sheetIdentity_eq_one (B := B)] using sheetGamma_sq (B := B)
  exchange_sq := by
    simpa only [sheetIdentity_eq_one (B := B)] using sheetJ_sq (B := B)
  exchange_gamma_anticomm := sheetJ_mul_sheetGamma (B := B)

theorem represented_witt_car :
    wittPlus (sheetGamma (B := B)) (sheetJ (B := B)) *
        wittMinus (sheetGamma (B := B)) (sheetJ (B := B)) +
      wittMinus (sheetGamma (B := B)) (sheetJ (B := B)) *
        wittPlus (sheetGamma (B := B)) (sheetJ (B := B)) = 1 :=
  witt_car (Γ := sheetGamma (B := B)) (J := sheetJ (B := B))

end InfoGeometry.Optics.OperatorCl11JonesRepresentation
