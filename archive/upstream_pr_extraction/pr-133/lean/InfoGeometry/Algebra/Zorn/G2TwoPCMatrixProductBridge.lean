import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate

namespace InfoGeometry.Algebra.Zorn.G2TwoPCMatrixProductBridge

open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

theorem pcWord_mul_eq_pcCombine_bridge (e f : PCExponent) :
    pcWord e * pcWord f = pcWord (pcCombine e f) := by
  exact pcWord_mul_pcWord e f

theorem matrixWord_mul_matrixWord_bridge (e f : PCExponent) :
    matrixWord f * matrixWord e = matrixWord (pcCombine e f) := by
  rw [← autMatrix_pcWord, ← autMatrix_pcWord, ← autMatrix_mul]
  rw [pcWord_mul_eq_pcCombine_bridge]
  rw [autMatrix_pcWord]

end InfoGeometry.Algebra.Zorn.G2TwoPCMatrixProductBridge
