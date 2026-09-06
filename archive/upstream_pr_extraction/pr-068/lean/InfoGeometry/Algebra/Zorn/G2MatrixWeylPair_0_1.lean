import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate

namespace InfoGeometry.Algebra.Zorn.G2MatrixWeylPair_0_1

open Matrix
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def cMatrix : Matrix (Fin 8) (Fin 8) F2 :=
  cycle012Matrix * swapCartanMatrix

def sMatrix : Matrix (Fin 8) (Fin 8) F2 := swap01Matrix

abbrev LocalWeylG2 := ZMod 6 × Bool

def weylMatrix (p : LocalWeylG2) : Matrix (Fin 8) (Fin 8) F2 :=
  if p.2 then cMatrix ^ p.1.val * sMatrix else cMatrix ^ p.1.val

theorem matrix_weyl_entry_separation_0_1 (e d : PCExponent) :
    ∃ i j : Fin 8,
      (matrixWord d * weylMatrix ((0, false) : LocalWeylG2) * matrixWord e) i j ≠
        weylMatrix ((1, false) : LocalWeylG2) i j := by
  fin_cases e <;> fin_cases d <;> decide

end InfoGeometry.Algebra.Zorn.G2MatrixWeylPair_0_1
