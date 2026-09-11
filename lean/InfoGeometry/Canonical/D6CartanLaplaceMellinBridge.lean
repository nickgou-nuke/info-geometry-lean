import InfoGeometry.Canonical.D6CartanReciprocalTorus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Laplace/Mellin character bridge on the rank-two Cartan torus

The additive Cartan character and its multiplicative reciprocal readout are
identified through logarithmic coordinates.  This is a kernel identity, not a
claim that an integral transform or a continuum spectral theorem has been
constructed.
-/

namespace InfoGeometry.Canonical.D6CartanLaplaceMellinBridge

open InfoGeometry.Canonical.D6CartanReciprocalTorus

noncomputable section

abbrev SpectralTriple := ℝ × ℝ × ℝ

def laplaceKernel (s : SpectralTriple) (t : CartanPair) : ℝ :=
  Real.exp (-(s.1 * t.1 + s.2.1 * t.2 + s.2.2 * (-(t.1 + t.2))))

def mellinKernel (s : SpectralTriple) (z : TorusTriple) : ℝ :=
  Real.exp (-((s.1 / 2) * Real.log z.1 +
    (s.2.1 / 2) * Real.log z.2.1 +
    (s.2.2 / 2) * Real.log z.2.2))

theorem laplaceKernel_eq_mellinKernel_on_cartanTorus
    (s : SpectralTriple) (t : CartanPair) :
    laplaceKernel s t = mellinKernel s (cartanTorus t) := by
  unfold laplaceKernel mellinKernel
  simp [cartanTorus, Real.log_exp]
  ring

theorem laplaceKernel_reduced (s : SpectralTriple) (t : CartanPair) :
    laplaceKernel s t =
      Real.exp (-((s.1 - s.2.2) * t.1 + (s.2.1 - s.2.2) * t.2)) := by
  unfold laplaceKernel
  congr 1
  ring

theorem cartanTorus_log_sum_zero (t : CartanPair) :
    Real.log (cartanTorusComponent 0 t) +
      Real.log (cartanTorusComponent 1 t) +
      Real.log (cartanTorusComponent 2 t) = 0 := by
  rw [cartanTorus_log t 0, cartanTorus_log t 1, cartanTorus_log t 2]
  ring

end
end InfoGeometry.Canonical.D6CartanLaplaceMellinBridge
