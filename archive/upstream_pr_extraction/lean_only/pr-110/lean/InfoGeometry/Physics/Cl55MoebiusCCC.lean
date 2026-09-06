import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.Cl44FockParity
import InfoGeometry.Physics.SplitCliffordAlgebras

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

/-! ## 1. Finite parity shadow used by the readout -/

theorem cl44_witten_index_zero : ((8 : ℤ) - 8) = 0 := by
  exact InfoGeometry.OperatorAlgebra.Cl44FockParity.witten_index_zero

/-! ## 2. Chiral parity compensation -/

/-- A finite integer readout for the chiral parity balance. -/
theorem chiral_parity_compensation : ((16 : ℤ) - 16) = 0 := by
  norm_num

/-- The arithmetic parity balance transported from the existing finite
`Cl(4,4)` chiral-sheet dimension readout.  This uses the supplied dimension
definition only; it does not assert an intrinsic half-spin decomposition. -/
theorem chiral_sheet_dimension_parity_compensation :
    ((SplitClifford.chiralSheetDim : ℤ) - SplitClifford.chiralSheetDim) = 0 := by
  rw [SplitClifford.chiralSheetDim_eq_16]
  norm_num

/-! ## 3. The finite packet contains no further structure -/

/-- The two finite parity readouts packaged together.

This conjunction is only an arithmetic packet: it does not identify the two
terms with dimensions of a proved chiral representation. -/
theorem finite_parity_packet :
    (((8 : ℤ) - 8) = 0) ∧ (((16 : ℤ) - 16) = 0) := by
  exact ⟨cl44_witten_index_zero, chiral_parity_compensation⟩

end InfoGeometry.Physics.Cl55MoebiusCCC
