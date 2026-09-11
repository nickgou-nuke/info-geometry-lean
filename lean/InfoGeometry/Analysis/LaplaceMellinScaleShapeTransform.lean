import InfoGeometry.Analysis.LaplaceFourierComparison
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform

Scale-shape bridge.

This file uses the native Laplace and Mellin transforms to keep the
multiplicative scale channel and additive log-time shape channel distinct.

The intended interpretation is:

* Mellin channel = multiplicative scale variable;
* Laplace channel = additive shape / defect variable;
* the operator split from the canonical file is the ambient spine.

It does not assert any prime-number, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform

/-! The scale-shape carrier is the additive log-time signal itself. The former
packet added no data or law beyond `signal`. -/
@[rep_depth operator]
abbrev LaplaceMellinScaleShapePacket := ℝ → ℂ

namespace LaplaceMellinScaleShapePacket

open InfoGeometry.Analysis
open InfoGeometry.Analysis.LaplaceTransform
open InfoGeometry.Analysis.LaplaceFourierComparison

/-- Multiplicative-scale Mellin channel obtained from the log-time signal. -/
@[rep_depth operator]
def scaleChannel (P : LaplaceMellinScaleShapePacket) : ℂ → ℂ :=
  mellin (fun r : ℝ => P (-Real.log r))

/-- Additive log-time Laplace channel. -/
@[rep_depth operator]
def shapeChannel (P : LaplaceMellinScaleShapePacket) : ℂ → ℂ :=
  laplaceTransform P

/--
The Mellin scale channel is the Laplace shape channel after logarithmic
pullback.  This is the native change-of-variables theorem owned by
`LaplaceFourierComparison`.
-/
@[rep_depth operator]
theorem mellinScaleCompatible (P : LaplaceMellinScaleShapePacket) :
    P.scaleChannel = P.shapeChannel := by
  funext s
  exact mellin_logPullback_eq_laplaceTransform (f := P) (s := s)

/-- Symmetric readback of logarithmic Laplace--Mellin compatibility. -/
@[rep_depth operator]
theorem laplaceShapeCompatible (P : LaplaceMellinScaleShapePacket) :
    P.shapeChannel = P.scaleChannel :=
  P.mellinScaleCompatible.symm

/-- The ordered pair keeps the multiplicative and additive channels explicit. -/
@[rep_depth operator]
def channels (P : LaplaceMellinScaleShapePacket) : (ℂ → ℂ) × (ℂ → ℂ) :=
  (P.scaleChannel, P.shapeChannel)

/-- Native product-projection law for the scale/shape block split. -/
@[rep_depth operator]
theorem scaleShapeBlockSplit (P : LaplaceMellinScaleShapePacket) :
    P.channels.1 = P.scaleChannel ∧ P.channels.2 = P.shapeChannel :=
  ⟨rfl, rfl⟩

end LaplaceMellinScaleShapePacket

end InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform
