import InfoGeometry.Canonical.SplitHypercomplexStructure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Left-hyperbolic notation for the split Cayley--Dickson basis

The canonical integral owner names `ilOct`, `jlOct`, and `klOct` for the
right-attached products `i*l`, `j*l`, and `k*l`.  This file exposes the
left-attached notation `l*i`, `l*j`, and `l*k` without changing that owner.
The sign is forced by the Cayley--Dickson conjugation twist.
-/

namespace InfoGeometry.Canonical.SplitCayleyDicksonLeftQuaternionBridge

open InfoGeometry.Canonical

def leftLi : StandardIntegralSplitOctonion := -ilOct

def leftLj : StandardIntegralSplitOctonion := -jlOct

def leftLk : StandardIntegralSplitOctonion := -klOct

theorem l_mul_i_eq_leftLi :
    splitOctonionMul lOct iOct = leftLi := by
  simpa [leftLi] using l_mul_i_eq_neg_il

theorem l_mul_j_eq_leftLj :
    splitOctonionMul lOct jOct = leftLj := by
  dsimp [leftLj, lOct, jOct, jlOct, splitBasisVector,
    splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

theorem l_mul_k_eq_leftLk :
    splitOctonionMul lOct kOct = leftLk := by
  dsimp [leftLk, lOct, kOct, klOct, splitBasisVector,
    splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

theorem leftLi_null_minus_sq :
    splitOctonionMul (iOct + leftLi) (iOct + leftLi) = 0 := by
  simpa [leftLi] using hypercomplexNullMinus_sq

theorem leftLj_null_minus_sq :
    splitOctonionMul (jOct + leftLj) (jOct + leftLj) = 0 := by
  dsimp [leftLj, jOct, jlOct, splitBasisVector,
    splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

theorem leftLk_null_minus_sq :
    splitOctonionMul (kOct + leftLk) (kOct + leftLk) = 0 := by
  dsimp [leftLk, kOct, klOct, splitBasisVector,
    splitOctonionMul, basisMul]
  ext r
  fin_cases r <;> decide

end InfoGeometry.Canonical.SplitCayleyDicksonLeftQuaternionBridge
