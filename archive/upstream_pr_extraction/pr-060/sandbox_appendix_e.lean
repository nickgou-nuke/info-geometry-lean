import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

namespace InfoGeometry.Lie.SplitOctonionAppendixEZeroDivisorBridge

abbrev O := SplitOctonionQuaternion
abbrev lUnit := InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit

-- Paper basis definitions
def paperI : O := lUnit
def paperj (n : Fin 3) : O := quaternionImaginary n
def paperJ (n : Fin 3) : O := - (lUnit * quaternionImaginary n) -- Since I * j_n = -J_n

-- Paper zero divisors
def paperDPlusI : O := 2⁻¹ • (1 + paperI)
def paperDMinusI : O := 2⁻¹ • (1 - paperI)

def paperGPlusJ (n : Fin 3) : O := 2⁻¹ • (paperJ n + paperj n)
def paperGMinusJ (n : Fin 3) : O := 2⁻¹ • (paperJ n - paperj n)

-- Calibration theorems
theorem paperDPlusI_eq_zornPlus : paperDPlusI = zornPlus := rfl
theorem paperDMinusI_eq_zornMinus : paperDMinusI = zornMinus := rfl

theorem paperGPlusJ_eq_neg_rootMinus (n : Fin 3) : paperGPlusJ n = - rootMinus n := by
  dsimp [paperGPlusJ, paperJ, paperj, rootMinus]
  -- we need to check if 2⁻¹ • (- (lUnit * e_n) + e_n) = - 2⁻¹ • (lUnit * e_n - e_n)
  -- Wait, rootMinus is 2⁻¹ • (lUnit * e_n - e_n). So it's exactly -rootMinus.
  sorry

theorem paperGMinusJ_eq_neg_rootPlus (n : Fin 3) : paperGMinusJ n = - rootPlus n := by
  dsimp [paperGMinusJ, paperJ, paperj, rootPlus]
  sorry

end InfoGeometry.Lie.SplitOctonionAppendixEZeroDivisorBridge
