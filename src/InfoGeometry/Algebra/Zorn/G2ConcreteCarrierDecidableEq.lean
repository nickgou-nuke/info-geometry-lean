import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Computational equality on the concrete `G₂(2)` carrier

The native automorphism carrier already has a finite enumeration.  This owner
supplies its computational equality by transporting matrix equality through
the proved injectivity of `autMatrix`.
-/

namespace InfoGeometry.Algebra.Zorn.G2ConcreteCarrierDecidableEq

open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

instance splitOctF2AutDecidableEq : DecidableEq SplitOctF2Aut := by
  intro f g
  by_cases h : autMatrix f = autMatrix g
  · exact isTrue (autMatrix_injective h)
  · exact isFalse (fun hfg => h (congrArg autMatrix hfg))

end InfoGeometry.Algebra.Zorn.G2ConcreteCarrierDecidableEq
