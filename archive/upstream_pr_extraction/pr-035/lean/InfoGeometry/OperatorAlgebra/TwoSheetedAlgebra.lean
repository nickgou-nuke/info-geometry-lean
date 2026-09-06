import Mathlib

open MulOpposite

namespace InfoGeometry.OperatorAlgebra

/-- Two-sheeted operator algebra with commutant structure.
    Represents the (M, M') pair from Tomita-Takesaki theory,
    or the (Cl⁺, Cl⁻) pair in chiral setups.
-/
structure TwoSheetedAlgebra (K : Type*) [CommRing K] where
  L : Type*
  R_alg : Type*
  [instL : Ring L]
  [instR : Ring R_alg]
  [instAlgL : Algebra K L]
  [instAlgR : Algebra K R_alg]
  /-- Commutant embedding (Tomita J-action mapping M to M')
      Modeled here as an equivalence between L and the opposite ring of R_alg -/
  commutant : L ≃+* R_algᵐᵒᵖ

end InfoGeometry.OperatorAlgebra
