import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Analysis.LaplaceFourierComparison

/-!
# Complexified Cartan kernel

This file records the finite kernel identity behind the complex spectral
parameter `σ + τ I`.  It does not construct a Harish--Chandra transform,
principal-series representation, or noncommutative Fourier theory.  The
existing Mellin/Laplace and Fourier comparison owners remain responsible for
those analytic interfaces.
-/

namespace InfoGeometry.Analysis.ComplexifiedCartanMellinKernel

open InfoGeometry.Analysis.LaplaceTransform

/-- The complexified split/compact spectral parameter. -/
def complexifiedSpectralParameter (σ τ : ℝ) : ℂ :=
  (σ : ℂ) + (τ : ℂ) * Complex.I

@[simp] theorem complexifiedSpectralParameter_re (σ τ : ℝ) :
    (complexifiedSpectralParameter σ τ).re = σ := by
  simp [complexifiedSpectralParameter]

@[simp] theorem complexifiedSpectralParameter_im (σ τ : ℝ) :
    (complexifiedSpectralParameter σ τ).im = τ := by
  simp [complexifiedSpectralParameter]

/--
The native Laplace kernel splits into its real damping and imaginary phase
factors at a complexified spectral parameter.
-/
theorem laplaceKernel_complexified_split (σ τ t : ℝ) :
    laplaceKernel (complexifiedSpectralParameter σ τ) t =
      Complex.exp (-(σ : ℂ) * (t : ℂ)) *
        Complex.exp (-((τ : ℂ) * (t : ℂ)) * Complex.I) := by
  rw [laplaceKernel]
  have h :
      -(complexifiedSpectralParameter σ τ * (t : ℂ)) =
        (-(σ : ℂ) * (t : ℂ)) +
          (-((τ : ℂ) * (t : ℂ)) * Complex.I) := by
    simp [complexifiedSpectralParameter]
    ring
  rw [h, Complex.exp_add]

end InfoGeometry.Analysis.ComplexifiedCartanMellinKernel
