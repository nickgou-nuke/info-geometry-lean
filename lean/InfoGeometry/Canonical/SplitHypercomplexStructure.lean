import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
Concrete split-hypercomplex data in the named integral basis.  The generators
are definitions, not fields carrying multiplication laws as assumptions.
-/

def splitHypercomplexI : StandardIntegralSplitOctonion := iOct
def splitHypercomplexL : StandardIntegralSplitOctonion := lOct
def splitHypercomplexIL : StandardIntegralSplitOctonion := ilOct

def hypercomplexNullPlus : StandardIntegralSplitOctonion :=
  splitHypercomplexI + splitHypercomplexIL

def hypercomplexNullMinus : StandardIntegralSplitOctonion :=
  splitHypercomplexI - splitHypercomplexIL

theorem splitHypercomplexI_sq :
    splitOctonionMul splitHypercomplexI splitHypercomplexI = -oneOct := by
  dsimp [splitHypercomplexI, iOct, oneOct, splitBasisVector,
    splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

theorem splitHypercomplexL_sq :
    splitOctonionMul splitHypercomplexL splitHypercomplexL = oneOct := by
  dsimp [splitHypercomplexL, lOct, oneOct, splitBasisVector,
    splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

theorem splitHypercomplexIL_sq :
    splitOctonionMul splitHypercomplexIL splitHypercomplexIL = oneOct := by
  dsimp [splitHypercomplexIL, ilOct, oneOct, splitBasisVector,
    splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

theorem hypercomplexNullPlus_sq :
    splitOctonionMul hypercomplexNullPlus hypercomplexNullPlus = 0 := by
  dsimp [hypercomplexNullPlus, splitHypercomplexI, splitHypercomplexIL,
    iOct, ilOct, splitBasisVector, splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

theorem hypercomplexNullMinus_sq :
    splitOctonionMul hypercomplexNullMinus hypercomplexNullMinus = 0 := by
  dsimp [hypercomplexNullMinus, splitHypercomplexI, splitHypercomplexIL,
    iOct, ilOct, splitBasisVector, splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

end InfoGeometry.Canonical
