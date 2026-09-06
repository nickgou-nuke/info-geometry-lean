import InfoGeometry.Analysis.CliffordWaveletTransform
import InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.MellinWaveletScaleShapeBridge

A narrow composition bridge between the existing logarithmic Laplace--Mellin
owner and the existing Clifford wavelet owner.

The bridge records two theorem-safe facts:

* the multiplicative Mellin scale channel equals the additive log-time Laplace
  channel by the native logarithmic pullback theorem;
* an admissible Clifford wavelet model reconstructs an encoded log-time signal.

This file does not identify transformer attention with quantum entanglement,
does not construct a mapping cylinder, and does not prove a logarithmic CFT or
conformal-cobordism theorem.  Those interpretations require additional native
operator-algebraic, topological, and conformal data.
-/

noncomputable section

namespace InfoGeometry.Analysis.MellinWaveletScaleShapeBridge

open InfoGeometry.Analysis.CliffordWaveletTransform
open InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform

/--
An adapter between an additive log-time signal and the signal carrier of an
existing Clifford wavelet model.

`decode_encode` states that no log-time information is lost by the adapter.
Wavelet reconstruction remains owned by `CliffordWaveletModel.admissible`.
-/
@[rep_depth operator]
structure LogTimeWaveletAdapter (W : CliffordWaveletModel) where
  encode : LaplaceMellinScaleShapePacket → W.Signal
  decode : W.Signal → LaplaceMellinScaleShapePacket
  decode_encode : Function.LeftInverse decode encode

namespace LogTimeWaveletAdapter

variable {W : CliffordWaveletModel}
variable (B : LogTimeWaveletAdapter W)

/-- Clifford wavelet coefficients of an encoded additive log-time signal. -/
@[rep_depth operator]
def waveletCoefficients
    (P : LaplaceMellinScaleShapePacket) :
    SimilitudeParameter W.V → CliffordCoefficient :=
  W.waveletTransform (B.encode P)

/-- Decode the wavelet reconstruction back to the additive log-time carrier. -/
@[rep_depth operator]
def reconstructedLogTimeSignal
    (P : LaplaceMellinScaleShapePacket) :
    LaplaceMellinScaleShapePacket :=
  B.decode (W.reconstruction (B.waveletCoefficients P))

/--
The native Mellin scale channel is the native Laplace channel after the
logarithmic pullback `r ↦ -log r`.
-/
@[rep_depth operator]
theorem mellin_scale_eq_laplace_shape
    (P : LaplaceMellinScaleShapePacket) :
    P.scaleChannel = P.shapeChannel :=
  P.mellinScaleCompatible

/-- An admissible wavelet model reconstructs every encoded log-time signal. -/
@[rep_depth operator]
theorem reconstructedLogTimeSignal_eq
    (hAdm : W.admissible)
    (P : LaplaceMellinScaleShapePacket) :
    B.reconstructedLogTimeSignal P = P := by
  unfold reconstructedLogTimeSignal waveletCoefficients
  rw [W.reconstruction_waveletTransform hAdm (B.encode P)]
  exact B.decode_encode P

/--
Combined scale/shape and wavelet-reconstruction packet.

The first component is analytic logarithmic compatibility; the second is the
wavelet left-inverse law transported through the log-time adapter.
-/
@[bridge_target_tag, rep_depth operator]
theorem mellin_wavelet_scale_shape_packet
    (hAdm : W.admissible)
    (P : LaplaceMellinScaleShapePacket) :
    P.scaleChannel = P.shapeChannel ∧
      B.reconstructedLogTimeSignal P = P :=
  ⟨B.mellin_scale_eq_laplace_shape P,
    B.reconstructedLogTimeSignal_eq hAdm P⟩

end LogTimeWaveletAdapter

end InfoGeometry.Analysis.MellinWaveletScaleShapeBridge

end noncomputable section
