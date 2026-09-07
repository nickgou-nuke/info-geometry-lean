import InfoGeometry.Canonical.BogoliubovCovariantMellinKreinQuantizationBridge
import InfoGeometry.Canonical.MoebiusBogoliubovVirasoroBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Mellin weights as Bogoliubov null eigenvalues

This is a thin arithmetic readback over the existing Möbius/Bogoliubov
owner.  For a mode `n` and centered Mellin coordinate `u`, the hyperbolic
rapidity is `u * log n`.  The two Witt/null eigenvalues are therefore
`n⁻ᵘ` and `nᵘ`; no new Fock space, CAR/CCR implementation, or infinite-mode
implementability claim is introduced here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MellinBogoliubovNullEigenvalueBridge

open InfoGeometry.Canonical.BogoliubovMellinKrein
open InfoGeometry.Canonical.MoebiusBogoliubovVirasoro
open InfoGeometry.Canonical.BogoliubovFockSuper

/-- The contracting null eigenvalue of the Mellin rapidity. -/
theorem mellin_null_eigenvalue_minus (n : ℕ) (u : ℝ)
    (hn : 0 < (n : ℝ)) :
    Real.cosh (bogoliubovRapidity n u) -
        Real.sinh (bogoliubovRapidity n u) =
      (n : ℝ) ^ (-u) := by
  rw [Real.cosh_sub_sinh]
  rw [Real.rpow_def_of_pos hn]
  congr 1
  dsimp [bogoliubovRapidity]
  ring

/-- The opposite Witt/null eigenvalue of the Mellin rapidity. -/
theorem mellin_null_eigenvalue_plus (n : ℕ) (u : ℝ)
    (hn : 0 < (n : ℝ)) :
    Real.cosh (bogoliubovRapidity n u) +
        Real.sinh (bogoliubovRapidity n u) =
      (n : ℝ) ^ u := by
  rw [Real.cosh_add_sinh]
  rw [Real.rpow_def_of_pos hn]
  congr 1
  dsimp [bogoliubovRapidity]
  ring

/-- Read the two Mellin null eigenvalues from the existing Möbius tilt. -/
theorem moebius_mellin_null_eigenvalues (n : ℕ) (u : ℝ)
    (hn : 0 < (n : ℝ)) :
    let B := bogoliubovTiltOfBoost
      (Real.exp (bogoliubovRapidity n u))
    B.u - B.v = (n : ℝ) ^ (-u) ∧
      B.u + B.v = (n : ℝ) ^ u := by
  simp only [bogoliubovTiltOfBoost, HyperbolicMixingParams.ofAngle,
    Real.log_exp]
  constructor
  · exact mellin_null_eigenvalue_minus n u hn
  · exact mellin_null_eigenvalue_plus n u hn

end InfoGeometry.Arithmetic.MellinBogoliubovNullEigenvalueBridge
