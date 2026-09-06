import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.QuantumGeometry.Projective
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# QGT Riemannian metric surface

This owner packages the real part of the projective quantum geometric tensor as
an honest metric surface:
- symmetry of `Re(QGT)`;
- nonnegativity on diagonal entries;
- coordinate-component packaging along a chosen finite operator frame.

We do not claim a full manifold-level `RiemannianMetric` structure here. The
kernel-checked content is exactly the bilinear/projective operator surface that
already follows from `QGT.lean`.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry.Projective.QGTRiemannian

open InfoGeometry.QuantumGeometry.Projective
open ContinuousLinearMap
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-- The projective Riemannian metric carried by the real part of the QGT. -/
abbrev qgtRiemannianMetric (ψ : NormalizedState H) (X Y : EndH) : ℝ :=
  fubiniStudyMetric ψ X Y

theorem qgtRiemannianMetric_symmetric (ψ : NormalizedState H) (X Y : EndH) :
    qgtRiemannianMetric ψ X Y = qgtRiemannianMetric ψ Y X := by
  rw [qgtRiemannianMetric, qgtRiemannianMetric]
  rw [fubiniStudyMetric, fubiniStudyMetric]
  rw [QGT_eq_inner_projOrth, QGT_eq_inner_projOrth]
  let u := projOrth ψ X
  let v := projOrth ψ Y
  have hinner :
      ⟪u, v⟫_ℂ = starRingEnd ℂ (⟪v, u⟫_ℂ) := by
    simpa [u, v] using inner_conj_symm v u
  calc
    (⟪u, v⟫_ℂ).re = (starRingEnd ℂ (⟪v, u⟫_ℂ)).re := by rw [hinner]
    _ = (⟪v, u⟫_ℂ).re := by simpa using Complex.conj_re (⟪v, u⟫_ℂ)

theorem qgtRiemannianMetric_self_nonneg (ψ : NormalizedState H) (X : EndH) :
    0 ≤ qgtRiemannianMetric ψ X X := by
  rw [qgtRiemannianMetric, fubiniStudyMetric_self_eq_normSq]
  positivity

theorem qgtRiemannianMetric_self_pos_of_projOrth_ne_zero
    (ψ : NormalizedState H) (X : EndH) (hX : projOrth ψ X ≠ 0) :
    0 < qgtRiemannianMetric ψ X X := by
  rw [qgtRiemannianMetric, fubiniStudyMetric_self_eq_normSq]
  have hnorm : 0 < ‖projOrth ψ X‖ := norm_pos_iff.mpr hX
  nlinarith [hnorm]

/-- Coordinate components of the QGT Riemannian metric along a finite operator frame. -/
def metricTensorComponents {n : ℕ}
    (ψ : NormalizedState H) (basis : Fin n → EndH) (μ ν : Fin n) : ℝ :=
  qgtRiemannianMetric ψ (basis μ) (basis ν)

theorem metricTensorComponents_symmetric {n : ℕ}
    (ψ : NormalizedState H) (basis : Fin n → EndH) (μ ν : Fin n) :
    metricTensorComponents ψ basis μ ν = metricTensorComponents ψ basis ν μ := by
  simp [metricTensorComponents, qgtRiemannianMetric_symmetric]

theorem metricTensorComponents_self_nonneg {n : ℕ}
    (ψ : NormalizedState H) (basis : Fin n → EndH) (μ : Fin n) :
    0 ≤ metricTensorComponents ψ basis μ μ := by
  simpa [metricTensorComponents] using
    qgtRiemannianMetric_self_nonneg (ψ := ψ) (X := basis μ)

/-- Honest packaged metric data extracted from the QGT real part. -/
structure MetricData (ψ : NormalizedState H) where
  metric : EndH → EndH → ℝ
  symmetric : ∀ X Y, metric X Y = metric Y X
  self_nonneg : ∀ X, 0 ≤ metric X X

/-- The real part of the QGT supplies symmetric positive-semidefinite metric data. -/
def qgtMetricData (ψ : NormalizedState H) : MetricData ψ where
  metric := qgtRiemannianMetric ψ
  symmetric := qgtRiemannianMetric_symmetric ψ
  self_nonneg := qgtRiemannianMetric_self_nonneg ψ

end InfoGeometry.QuantumGeometry.Projective.QGTRiemannian
