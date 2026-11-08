import InfoGeometry.Superalgebra.SplitOctonionTwistedParityElement

/-! A small audit surface for the exact parity-square contract. -/

namespace InfoGeometry.Superalgebra.WittenMoebiusParityAudit

open InfoGeometry.Superalgebra.MadelungNonassociativeVortex
open InfoGeometry.Superalgebra.WittenMoebiusParity

#print axioms parityElement_sq
#print axioms parityElement_involutive_of_unitCircle_pairing
#print axioms pairing_eq_neg_one_of_involutive
#print axioms diagonalParityReadout_parityElement

example (c s : ℝ) (u v : ColorVec3 ℝ)
    (h_circle : c ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0)
    (h_involutive :
      SplitOctonion.mul (parityElement c s u v) (parityElement c s u v) =
        SplitOctonion.one) :
    ColorVec3.dot u v = -1 :=
  pairing_eq_neg_one_of_involutive c s u v h_circle hs h_involutive

end InfoGeometry.Superalgebra.WittenMoebiusParityAudit
