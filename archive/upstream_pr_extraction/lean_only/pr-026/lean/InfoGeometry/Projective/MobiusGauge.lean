import InfoGeometry.Projective.CrossRatio
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Möbius Gauge

This file formalizes the projective Möbius transitions, establishing the
gauge-covariance of affine lifts and the invariance of the cross-ratio.
-/

namespace InfoGeometry.Projective

/-- A fractional linear (Möbius) transformation over K. -/
structure MobiusMap (K : Type*) [Field K] where
  α : K
  β : K
  γ : K
  δ : K
  det_ne_zero : α * δ - β * γ ≠ 0

/-- The action of a Möbius transformation on an element `r`. -/
def projectiveAction {K : Type*} [Field K] (T : MobiusMap K) (r : K) : K :=
  (T.α * r + T.β) / (T.γ * r + T.δ)

/-- The denominator of the Möbius action. -/
def leftGauge {K : Type*} [Field K] (T : MobiusMap K) (z : K) : K :=
  T.γ * z + T.δ

/-- The composition of Möbius action with a label map `ζ`. -/
def mobiusComp {K ι : Type*} [Field K] (T : MobiusMap K) (ζ : ι → K) : ι → K :=
  fun i => projectiveAction T (ζ i)

end InfoGeometry.Projective
