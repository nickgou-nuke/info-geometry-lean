import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.QuantumGeometry.Projective
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# QGT Riemannian Metric on Projective Hilbert Space

This module extracts the Riemannian metric structure from the real part of the 
Quantum Geometric Tensor (QGT) on the projective Hilbert space.

The QGT decomposes as:
  Q_ψ(X, Y) = g_ψ(X, Y) - (i/2) Ω_ψ(X, Y)

where:
- g_ψ(X, Y) = Re(Q_ψ(X, Y)) is the Fubini-Study Riemannian metric
- Ω_ψ(X, Y) = -2 Im(Q_ψ(X, Y)) is the Berry curvature (symplectic form)

This module formalizes g as a Riemannian metric on the projective manifold P(H).
-/

noncomputable

namespace InfoGeometry.QuantumGeometry.Projective.QGTRiemannian

open InfoGeometry.QuantumGeometry.Projective
open InfoGeometry.QuantumGeometry.Projective.QGT
open ContinuousLinearMap
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "EndH" => H →L[ℂ] H

/-- 
The Fubini-Study Riemannian metric as a symmetric bilinear form on the tangent space.

For a normalized state ψ and tangent vectors X, Y ∈ T_ψP(H) ≃ {X : EndH | ⟪ψ, Xψ⟫_ℂ ∈ iℝ},
the metric is:
  g_ψ(X, Y) = Re(Q_ψ(X, Y)) = Re(⟪Xψ, Yψ⟫_ℂ - ⟪Xψ, ψ⟫_ℂ⟪ψ, Yψ⟫_ℂ)

This is the real part of the QGT, which equals the Fubini-Study metric.
-/
def fubiniStudyMetricBilinear (ψ : NormalizedState H) (X Y : EndH) : ℝ :=
  fubiniStudyMetric ψ X Y

/-- 
THEOREM: Symmetry of the Fubini-Study Metric

The bilinear form g_ψ(X, Y) is symmetric:
  g_ψ(X, Y) = g_ψ(Y, X)
-/
theorem fubiniStudyMetric_symmetric (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric ψ X Y = fubiniStudyMetric ψ Y X := by
  have h₁ : (QGT ψ X Y).re = (QGT ψ Y X).re := by
    have h₁ : QGT ψ X Y = (QGT ψ Y X)† := by
      dsimp only [QGT]
      simp [inner_conj_symm, Complex.ext_iff, starRingEnd_apply, mul_comm]
      <;>
      ring_nf <;>
      simp_all [Complex.ext_iff, starRingEnd_apply, inner_conj_symm]
      <;>
      norm_num <;>
      aesop
    rw [h₁]
    simp [Complex.ext_iff, starRingEnd_apply, Complex.normSq]
    <;>
    ring_nf <;>
    simp_all [Complex.ext_iff, starRingEnd_apply]
    <;>
    norm_num <;>
    aesop
  simpa [fubiniStudyMetric] using h₁

/-- 
THEOREM: Positive Semidefiniteness of the Fubini-Study Metric

For any tangent vector X, g_ψ(X, X) ≥ 0.
-/
theorem fubiniStudyMetric_pos_def (ψ : NormalizedState H) (X : EndH) :
    0 ≤ fubiniStudyMetric ψ X X := by
  have h : (QGT ψ X X).re = ‖projOrth ψ X‖ ^ 2 := by
    have h₁ : fubiniStudyMetric ψ X X = ‖projOrth ψ X‖ ^ 2 := by
      rw [fubiniStudyMetric_self_eq_normSq]
    simpa [fubiniStudyMetric] using h₁
  rw [h]
  positivity

/-- 
THEOREM: Positive Definiteness on Horizontal Subspace

The restriction of g_ψ to the horizontal subspace {X | ⟪ψ, Xψ⟫_ℂ = 0} is positive definite.
If X ≠ 0 and ⟪ψ, Xψ⟫_ℂ = 0, then g_ψ(X, X) > 0.
-/
theorem fubiniStudyMetric_pos_def_horizontal (ψ : NormalizedState H) (X : EndH) 
    (hX : ⟪ψ.vec, X ψ.vec⟫_ℂ = 0) (hX_ne : X ≠ 0) :
    0 < fubiniStudyMetric ψ X X := by
  have h₁ : fubiniStudyMetric ψ X X = ‖projOrth ψ X‖ ^ 2 := by
    rw [fubiniStudyMetric_self_eq_normSq]
  rw [h₁]
  have h₂ : projOrth ψ X ≠ 0 := by
    intro h
    have h₂ : X ≠ 0 := by
      intro hX
      simp_all [projOrth]
      <;> aesop
    exact h₂
  exact norm_pos_iff.mpr h₂

/-- 
The Riemannian metric tensor in coordinates.

For a coordinate chart on P(H), the metric tensor components are:
  g_μν = fubiniStudyMetric ψ (∂_μ) (∂_ν)
-/
def metricTensorComponents (ψ : NormalizedState H) (basis : Fin n → (H →L[ℂ] H)) (μ ν : Fin n) : ℝ :=
  fubiniStudyMetric ψ (basis μ) (basis ν)

/-- 
THEOREM: Metric tensor is symmetric.

g_μν = g_νμ
-/
theorem metricTensor_symmetric (ψ : NormalizedState H) (basis : Fin n → (H →L[ℂ] H)) (μ ν : Fin n) :
    metricTensorComponents ψ basis μ ν = metricTensorComponents ψ basis ν μ := by
  simp [metricTensorComponents]
  have h₁ : (QGT ψ (basis μ) (basis ν)).re = (QGT ψ (basis ν) (basis μ)).re := by
    have h₁ : QGT ψ (basis μ) (basis ν) = (QGT ψ (basis ν) (basis μ))† := by
      dsimp only [QGT]
      simp [inner_conj_symm, Complex.ext_iff, starRingEnd_apply, mul_comm]
      <;>
      ring_nf <;>
      simp_all [Complex.ext_iff, starRingEnd_apply, inner_conj_symm]
      <;>
      norm_num <;>
      aesop
    rw [h₁]
    simp [Complex.ext_iff, starRingEnd_apply, Complex.normSq]
    <;>
    ring_nf <;>
    simp_all [Complex.ext_iff, starRingEnd_apply]
    <;>
    norm_num <;>
    aesop
  simpa [metricTensorComponents, fubiniStudyMetric] using h₁

end InfoGeometry.QuantumGeometry.Projective.QGTRiemannian