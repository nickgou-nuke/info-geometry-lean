import InfoGeometry.Analysis.CliffordWaveletTransform
import InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.MellinWaveletScaleShapeBridge

A narrow composition bridge between the existing logarithmic Laplace--Mellin
owner and the existing Clifford wavelet owner.
-/

noncomputable section

namespace InfoGeometry.Analysis.MellinWaveletScaleShapeBridge

open InfoGeometry.Analysis.CliffordWaveletTransform
open InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform

@[rep_depth operator]
structure LogTimeWaveletAdapter (W : CliffordWaveletModel) where
  encode : LaplaceMellinScaleShapePacket → W.Signal
  decode : W.Signal → LaplaceMellinScaleShapePacket
  decode_encode : Function.LeftInverse decode encode

namespace LogTimeWaveletAdapter

variable {W : CliffordWaveletModel}
variable (B : LogTimeWaveletAdapter W)

@[rep_depth operator]
def waveletCoefficients
    (P : LaplaceMellinScaleShapePacket) :
    SimilitudeParameter W.V → CliffordCoefficient :=
  W.waveletTransform (B.encode P)

@[rep_depth operator]
def reconstructedLogTimeSignal
    (P : LaplaceMellinScaleShapePacket) :
    LaplaceMellinScaleShapePacket :=
  B.decode (W.reconstruction (B.waveletCoefficients P))

@[rep_depth operator]
theorem mellin_scale_eq_laplace_shape
    (P : LaplaceMellinScaleShapePacket) :
    P.scaleChannel = P.shapeChannel :=
  P.mellinScaleCompatible

@[rep_depth operator]
theorem reconstructedLogTimeSignal_eq
    (hAdm : W.admissible)
    (P : LaplaceMellinScaleShapePacket) :
    B.reconstructedLogTimeSignal P = P := by
  unfold reconstructedLogTimeSignal waveletCoefficients
  rw [W.reconstruction_waveletTransform hAdm (B.encode P)]
  exact B.decode_encode P

@[rep_depth operator]
theorem mellin_wavelet_scale_shape_packet
    (hAdm : W.admissible)
    (P : LaplaceMellinScaleShapePacket) :
    P.scaleChannel = P.shapeChannel ∧
      B.reconstructedLogTimeSignal P = P :=
  ⟨mellin_scale_eq_laplace_shape P,
    reconstructedLogTimeSignal_eq B hAdm P⟩

end LogTimeWaveletAdapter

end InfoGeometry.Analysis.MellinWaveletScaleShapeBridge

end noncomputable section
