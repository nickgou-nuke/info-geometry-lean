import InfoGeometry.Arithmetic.RHQuantumStabilityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbert

open InfoGeometry.Arithmetic.RHQuantumStabilityBridge

structure FockVsMellinNormalizabilityData
    (FockState MellinState FockNorm MellinNorm : Type) where
  fockState : FockState
  mellinState : MellinState
  fockNorm : FockNorm
  mellinNorm : MellinNorm

structure MajoranaZeroModeNormalizabilityData
    (ZeroMode NormReadout : Type) where
  realPart : ℝ
  imaginaryHeight : ℝ
  zeroMode : ZeroMode
  normReadout : NormReadout
  realPart_eq_half : realPart = (1 / 2 : ℝ)

namespace MajoranaZeroModeNormalizabilityData

def mkCriticalLine (ZeroMode NormReadout : Type)
    (zeroMode : ZeroMode) (normReadout : NormReadout) (imaginaryHeight : ℝ) :
    MajoranaZeroModeNormalizabilityData ZeroMode NormReadout where
  realPart := 1 / 2
  imaginaryHeight := imaginaryHeight
  zeroMode := zeroMode
  normReadout := normReadout
  realPart_eq_half := by rfl

variable {ZeroMode NormReadout : Type}
variable (P : MajoranaZeroModeNormalizabilityData ZeroMode NormReadout)

theorem criticalLine : IsCriticalLineRealPart P.realPart := by
  simpa [IsCriticalLineRealPart] using P.realPart_eq_half

end MajoranaZeroModeNormalizabilityData

end InfoGeometry.Arithmetic.MajoranaPolyaHilbert
