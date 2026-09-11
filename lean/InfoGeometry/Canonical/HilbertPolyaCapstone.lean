import InfoGeometry.Quantum.HilbertPolya
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.HilbertPolyaCapstone

open InfoGeometry.Quantum.HilbertPolya

theorem capstone_hilbert_polya_synthesis (γ x : ℝ) (hx : 0 < x) (τ : ℝ) :
    (dilationEigenfunction γ x =
      ((Real.rpow x (-1 / 2) : ℝ) : ℂ) *
        cylinderPhaseMode γ (Real.log x)) ∧
    (‖cylinderPhaseMode γ τ‖ = 1) := by
  exact ⟨dilation_mode_factorization γ x hx, cylinder_mode_unitary γ τ⟩

end InfoGeometry.Canonical.HilbertPolyaCapstone
