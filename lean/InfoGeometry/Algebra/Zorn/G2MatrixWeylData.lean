import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate

namespace InfoGeometry.Algebra.Zorn.G2MatrixWeylData

open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

def cMatrix : Matrix (Fin 8) (Fin 8) F2 :=
  cycle012Matrix * swapCartanMatrix

def sMatrix : Matrix (Fin 8) (Fin 8) F2 := swap01Matrix

def weylMatrix (p : WeylG2) : Matrix (Fin 8) (Fin 8) F2 :=
  if p.2 then cMatrix ^ p.1.val * sMatrix else cMatrix ^ p.1.val

end InfoGeometry.Algebra.Zorn.G2MatrixWeylData
