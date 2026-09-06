import InfoGeometry.Quantum.PoincareBlochEquator

namespace InfoGeometry.Canonical.PoincareBlochEquatorCapstone

open InfoGeometry.Quantum.PoincareBlochEquator

theorem capstone_poincare_bloch_synthesis (σ : ℝ)
    (h_equator : isEquatorialBlochState (σ - 1/2)) :
    (stokesCircularAsymmetry (σ - 1/2) = 0 ↔ σ - 1/2 = 0) ∧
    (σ = 1 / 2) ∧
    (vacuumZeroPointEnergy = 1 / 2) :=
  grand_poincare_bloch_synthesis σ h_equator

end InfoGeometry.Canonical.PoincareBlochEquatorCapstone
