import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Sage basis readout for the canonical chiral operator envelope

The associative free algebra, generators, word charge, and word product are
owned by `InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope`.  This file
contains only the SageMath basis readout used by the Algebra layer.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

def chiralSageSymbol : Fin 8 → ChiralOperatorEnvelope ℝ
  | 0 => ofGenerator .pPlus + ofGenerator .pMinus
  | 1 => ofGenerator (.sMinus 0) - ofGenerator (.sPlus 0)
  | 2 => ofGenerator (.sMinus 1) - ofGenerator (.sPlus 1)
  | 3 => ofGenerator (.sMinus 2) - ofGenerator (.sPlus 2)
  | 4 => ofGenerator .pPlus - ofGenerator .pMinus
  | 5 => ofGenerator (.sPlus 0) + ofGenerator (.sMinus 0)
  | 6 => ofGenerator (.sPlus 1) + ofGenerator (.sMinus 1)
  | 7 => ofGenerator (.sPlus 2) + ofGenerator (.sMinus 2)

@[simp] theorem chiralSageSymbol_zero :
    chiralSageSymbol 0 =
      ofGenerator .pPlus + ofGenerator .pMinus :=
  rfl

@[simp] theorem chiralSageSymbol_four :
    chiralSageSymbol 4 =
      ofGenerator .pPlus - ofGenerator .pMinus :=
  rfl

end InfoGeometry.Algebra
