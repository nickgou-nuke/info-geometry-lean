import InfoGeometry.Canonical.MoebiusBogoliubovVirasoroBridge

/-!
# Centered Mellin coordinate welded to the existing Möbius/Bogoliubov owner

This file is deliberately a thin readout.  It does not introduce a second
Bogoliubov matrix or a Fock representation.  The centered real coordinate
`u` is sent to the positive diagonal Möbius parameter `η = exp u`, and the
existing logarithmic Möbius tilt is read back as the hyperbolic coefficients
`cosh u` and `sinh u`.
-/

noncomputable section

namespace InfoGeometry.Canonical.BogoliubovCenteredMellinMoebiusWeld

open InfoGeometry.Canonical.MoebiusBogoliubovVirasoro
open InfoGeometry.Canonical.BogoliubovFockSuper

def centeredMellinScale (u : ℝ) : ℝ := Real.exp u

theorem centeredMellinScale_pos (u : ℝ) :
    0 < centeredMellinScale u := by
  exact Real.exp_pos u

theorem centeredMellinScale_log (u : ℝ) :
    Real.log (centeredMellinScale u) = u := by
  exact Real.log_exp u

theorem centeredMellinTilt_components (u : ℝ) :
    let B := bogoliubovTiltOfBoost (centeredMellinScale u)
    B.u = Real.cosh u ∧ B.v = Real.sinh u := by
  dsimp [bogoliubovTiltOfBoost, centeredMellinScale,
    HyperbolicMixingParams.ofAngle]
  simp [Real.log_exp]

/-! The two null/Witt eigenvalues of the hyperbolic tilt. -/

theorem centeredMellinTilt_null_eigenvalues (u : ℝ) :
    let B := bogoliubovTiltOfBoost (centeredMellinScale u)
    B.u + B.v = Real.exp u ∧ B.u - B.v = Real.exp (-u) := by
  have h := centeredMellinTilt_components u
  dsimp at h ⊢
  rw [h.1, h.2, Real.cosh_add_sinh, Real.cosh_sub_sinh]
  exact ⟨rfl, rfl⟩

def mellinPrimeContractingWeight (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-u * Real.log (n : ℝ))

/-- The Mellin decay factor is the contracting null eigenvalue of the
hyperbolic Bogoliubov tilt at rapidity `u * log n`. -/
theorem mellinPrimeContractingWeight_eq_null_eigenvalue (n : ℕ) (u : ℝ) :
    mellinPrimeContractingWeight n u =
      Real.cosh (u * Real.log (n : ℝ)) -
        Real.sinh (u * Real.log (n : ℝ)) := by
  unfold mellinPrimeContractingWeight
  rw [Real.cosh_sub_sinh]
  congr 1
  ring

/-- The opposite Mellin scale is the expanding null eigenvalue. -/
theorem mellinPrimeExpandingWeight_eq_null_eigenvalue (n : ℕ) (u : ℝ) :
    Real.exp (u * Real.log (n : ℝ)) =
      Real.cosh (u * Real.log (n : ℝ)) +
        Real.sinh (u * Real.log (n : ℝ)) := by
  rw [Real.cosh_add_sinh]

theorem centeredMellinTilt_unmixed_iff (u : ℝ) :
    (bogoliubovTiltOfBoost (centeredMellinScale u)).v = 0 ↔ u = 0 := by
  simp [bogoliubovTiltOfBoost, centeredMellinScale,
    HyperbolicMixingParams.ofAngle, Real.log_exp]

theorem centeredMellinCritical_readout :
    let B := bogoliubovTiltOfBoost (centeredMellinScale 0)
    B.u = 1 ∧ B.v = 0 := by
  simp [bogoliubovTiltOfBoost, centeredMellinScale,
    HyperbolicMixingParams.ofAngle]

end InfoGeometry.Canonical.BogoliubovCenteredMellinMoebiusWeld
