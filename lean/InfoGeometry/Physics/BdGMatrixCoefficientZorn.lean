import InfoGeometry.Physics.BdGValuedZornCarrier
import InfoGeometry.Physics.ZornMultiplicationOverBdG

/-!
# Matrix-coefficient Zorn system

This owner records the concrete noncommutative coefficient property for the
canonical matrix-valued Zorn carrier.  The coefficient algebra is
`Matrix (Fin 2) (Fin 2) ℚ`; no associativity, alternativity, Clifford module,
or physical representation theorem is asserted for the outer carrier.
-/

namespace InfoGeometry.Physics.PalatialTwistor

open InfoGeometry.Physics
open InfoGeometry.Physics.NCG

@[simp] theorem finrank_bdgMatrixCoefficientZorn :
    Module.finrank ℚ BdGValuedZornVectorCarrier = 32 :=
  finrank_bdgValuedZornVectorCarrier

end InfoGeometry.Physics.PalatialTwistor
