import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-!
# Appendix E Zero Divisors Bridge

This file provides the exact translation dictionary between the primitive idempotents
and nilpotents (zero divisors) defined in Appendix E of
Gogberashvili-Sakhelashvili (arXiv:1506.01012v2) and the `CanonicalZorn` circular basis.

We adopt the mapping:
- `1` ↔ `quaternionScalar`
- `I` ↔ `ellScalar`
- `j_n` ↔ `quaternionAxis n`
- `J_n` ↔ `-ellAxis n` (since `I * j_n = -J_n` and `ell * e_n = ell e_n`)
-/

namespace InfoGeometry.Lie.SplitOctonionAppendixEZeroDivisorBridge

abbrev CC := CartesianCoordinates

noncomputable section

def paperI : CC := ellScalar
def paperj (n : Fin 3) : CC := quaternionAxis n
def paperJ (n : Fin 3) : CC := -ellAxis n

-- Idempotents D±(I)
def paperDPlusI : CC := (1/2 : ℝ) • (quaternionScalar + paperI)
def paperDMinusI : CC := (1/2 : ℝ) • (quaternionScalar - paperI)

-- Nilpotents G±(J)
def paperGPlusJ (n : Fin 3) : CC := (1/2 : ℝ) • (paperJ n + paperj n)
def paperGMinusJ (n : Fin 3) : CC := (1/2 : ℝ) • (paperJ n - paperj n)

theorem paperDPlusI_eq_scalarPlus : paperDPlusI = scalarPlus := by
  dsimp [paperDPlusI, paperI, scalarPlus, quaternionScalar, ellScalar]

theorem paperDMinusI_eq_scalarMinus : paperDMinusI = scalarMinus := by
  dsimp [paperDMinusI, paperI, scalarMinus, quaternionScalar, ellScalar]

theorem paperGPlusJ_eq_neg_rootMinus (n : Fin 3) : paperGPlusJ n = - rootMinus n := by
  dsimp [paperGPlusJ, paperJ, paperj, rootMinus, quaternionAxis, ellAxis]
  ext <;> simp <;> ring

theorem paperGMinusJ_eq_neg_rootPlus (n : Fin 3) : paperGMinusJ n = - rootPlus n := by
  dsimp [paperGMinusJ, paperJ, paperj, rootPlus, quaternionAxis, ellAxis]
  ext <;> simp <;> ring

end

end InfoGeometry.Lie.SplitOctonionAppendixEZeroDivisorBridge
