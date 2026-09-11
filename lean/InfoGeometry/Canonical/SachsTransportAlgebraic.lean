import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic Sachs transport

This owner records the finite-dimensional consequence of a prescribed
transport law.  It does not derive the law from a Dirac equation or assert a
geometric horizon model.
-/

namespace InfoGeometry.Canonical.SachsTransportAlgebraic

noncomputable section

structure RayAmplitude where
  upper : ℝ
  lower : ℝ

def normSq (χ : RayAmplitude) : ℝ := χ.upper ^ 2 + χ.lower ^ 2

def transport (θ : ℝ) (χ : RayAmplitude) : RayAmplitude where
  upper := -(θ / 2) * χ.upper
  lower := -(θ / 2) * χ.lower

def kreinSq (χ : RayAmplitude) : ℝ := χ.upper ^ 2 - χ.lower ^ 2

theorem normSq_transport_rate (θ : ℝ) (χ : RayAmplitude) :
    2 * χ.upper * (transport θ χ).upper +
      2 * χ.lower * (transport θ χ).lower = -θ * normSq χ := by
  simp [transport, normSq]
  ring

theorem kreinSq_transport_rate (θ : ℝ) (χ : RayAmplitude) :
    2 * χ.upper * (transport θ χ).upper -
      2 * χ.lower * (transport θ χ).lower = -θ * kreinSq χ := by
  simp [transport, kreinSq]
  ring

theorem krein_null_transport_rate (θ : ℝ) (χ : RayAmplitude)
    (hχ : kreinSq χ = 0) :
    2 * χ.upper * (transport θ χ).upper -
      2 * χ.lower * (transport θ χ).lower = 0 := by
  rw [kreinSq_transport_rate, hχ, mul_zero]

theorem flux_rate_zero (area θ : ℝ) (χ : RayAmplitude) :
    (θ * area) * normSq χ + area * (-θ * normSq χ) = 0 := by
  ring

theorem scaled_null_state (A c : ℝ) :
    kreinSq ⟨A * c, A * c⟩ = 0 := by
  simp [kreinSq]

end

end InfoGeometry.Canonical.SachsTransportAlgebraic
