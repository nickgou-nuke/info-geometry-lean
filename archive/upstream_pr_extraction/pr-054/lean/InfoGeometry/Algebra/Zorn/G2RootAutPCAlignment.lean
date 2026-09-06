import InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
import InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts

namespace InfoGeometry.Algebra.Zorn.G2RootAutPCAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2Unipotent
open InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix

section PCWordExpressions

def shortOnePCExp : Fin 6 → Bool := oneAt 2
def shortTwoPCExp : Fin 6 → Bool := oneAt 0
def longTwoPCExp : Fin 6 → Bool := fun i => i = 2 || i = 5
def shortThreePCExp : Fin 6 → Bool := fun i => i = 0 || i = 1 || i = 4
def longThreePCExp : Fin 6 → Bool := fun i => i = 1 || i = 2
def longFourPCExp : Fin 6 → Bool := fun i => i = 1 || i = 3

end PCWordExpressions

end InfoGeometry.Algebra.Zorn.G2RootAutPCAlignment
