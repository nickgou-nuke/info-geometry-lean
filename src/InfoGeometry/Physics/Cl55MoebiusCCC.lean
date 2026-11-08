import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CliffordCAR
import InfoGeometry.OperatorAlgebra.Cl44FockParity
import InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws
import InfoGeometry.OperatorAlgebra.FullO55MatrixLaws
import InfoGeometry.Physics.OrbitClassification55
import InfoGeometry.Physics.WeightGrading55

/-!
# Cl(5,5) finite parity readout

This file records only the finite parity equalities proved below:

* the `Cl(4,4)` packet has vanishing Witten index;
* the chiral `16₊/16₋` packet is balanced as an integer equality;
* the packaged product is just a finite arithmetic readout.

It does **not** prove a conformal cyclic cosmology theorem, a `Pin(5,5)`/`O(5,5)`
identification, a projective sheet-pairing theorem, or any geometric statement
about future infinity or a next aeon.
-/

namespace InfoGeometry.Physics.Cl55MoebiusCCC

open InfoGeometry.OperatorAlgebra.CliffordCAR
open InfoGeometry.Physics.OrbitClassification55
open InfoGeometry.Physics.WeightGrading55

/-! ## 1. Finite parity shadow used by the readout -/

theorem cl44_witten_index_zero : ((8 : ℤ) - 8) = 0 := by
  exact InfoGeometry.OperatorAlgebra.Cl44FockParity.witten_index_zero

/-! ## 2. Chiral parity compensation -/

/-- A finite integer readout for the chiral parity balance. -/
theorem chiral_parity_compensation : ((16 : ℤ) - 16) = 0 := by
  norm_num

end InfoGeometry.Physics.Cl55MoebiusCCC
