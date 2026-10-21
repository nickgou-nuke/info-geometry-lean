/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.CrossRatio
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- The difference of two fractional-linear images.

This is the exact determinant-over-gauges identity used to prove that a
Möbius relabeling preserves nondegenerate affine charts. -/
theorem projectiveAction_sub
    {K : Type*} [Field K] (T : MobiusMap K) (x y : K)
    (hx : leftGauge T x ≠ 0) (hy : leftGauge T y ≠ 0) :
    projectiveAction T x - projectiveAction T y =
      (T.α * T.δ - T.β * T.γ) * (x - y) /
        (leftGauge T x * leftGauge T y) := by
  have hx' : T.γ * x + T.δ ≠ 0 := by
    simpa [leftGauge, mul_comm] using hx
  have hy' : T.γ * y + T.δ ≠ 0 := by
    simpa [leftGauge, mul_comm] using hy
  have hx'' : x * T.γ + T.δ ≠ 0 := by simpa [mul_comm] using hx'
  have hy'' : y * T.γ + T.δ ≠ 0 := by simpa [mul_comm] using hy'
  have hxy : (T.γ * x + T.δ) * (T.γ * y + T.δ) ≠ 0 :=
    mul_ne_zero hx' hy'
  have hxy'' : (x * T.γ + T.δ) * (y * T.γ + T.δ) ≠ 0 :=
    mul_ne_zero hx'' hy''
  unfold projectiveAction leftGauge
  field_simp [hx', hy', hx'', hy'', hxy, hxy'']
  ring_nf

/-- A nondegenerate fractional-linear action preserves separated affine points. -/
theorem projectiveAction_sub_ne_zero
    {K : Type*} [Field K] (T : MobiusMap K) (x y : K)
    (hx : leftGauge T x ≠ 0) (hy : leftGauge T y ≠ 0)
    (hxy : x - y ≠ 0) :
    projectiveAction T x - projectiveAction T y ≠ 0 := by
  rw [projectiveAction_sub T x y hx hy]
  exact div_ne_zero
    (mul_ne_zero T.det_ne_zero hxy)
    (mul_ne_zero hx hy)

/-- The composition of Möbius action with a label map `ζ`. -/
def mobiusComp {K ι : Type*} [Field K] (T : MobiusMap K) (ζ : ι → K) : ι → K :=
  fun i => projectiveAction T (ζ i)

end InfoGeometry.Projective
