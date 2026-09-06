import InfoGeometry.Arithmetic.MellinBogoliubovMatrixReadoutBridge

/-!
# Finite covariance packet for Mellin Bogoliubov modes

This owner only composes the existing finite matrix and arithmetic readouts.
For a mode `n > 1`, its centered Mellin rapidity has determinant-one matrix
readout, inverse squeezing, reciprocal null eigenvalues, and the critical-line
fixed-point criterion.  No Fock implementer, infinite-mode product, or
analytic limiting statement is introduced.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MellinBogoliubovFiniteCovarianceBridge

open InfoGeometry.Arithmetic.MellinBogoliubovNullEigenvalueBridge
open InfoGeometry.Arithmetic.MellinBogoliubovMatrixReadoutBridge
open InfoGeometry.Canonical.BogoliubovMellinKrein

theorem finite_mellin_bogoliubov_covariant_readout
    (n : ℕ) (u t : ℝ) (hn : 1 < n) :
    let r := bogoliubovRapidity n u
    (bogoliubovMatrix u t (Real.log (n : ℝ))).det = 1 ∧
      squeezingMatrix (-r) * squeezingMatrix r = 1 ∧
      (squeezingMatrix r = 1 ↔ u = 0) ∧
      squeezingMatrix r 0 0 - squeezingMatrix r 0 1 =
        (((n : ℝ) ^ (-u) : ℝ) : ℂ) ∧
      squeezingMatrix r 0 0 + squeezingMatrix r 0 1 =
        (((n : ℝ) ^ u : ℝ) : ℝ) := by
  dsimp
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hn
  have hfinite := finite_bogoliubov_mellin_readout
    u t (Real.log (n : ℝ)) hlog_pos
  have hminus := squeezingMatrix_mellin_null_eigenvalue_minus n u
    (by exact_mod_cast (Nat.zero_lt_of_lt hn))
  have hplus := squeezingMatrix_mellin_null_eigenvalue_plus n u
    (by exact_mod_cast (Nat.zero_lt_of_lt hn))
  exact ⟨hfinite.1, hfinite.2.1, hfinite.2.2.1,
    hminus, hplus⟩

end InfoGeometry.Arithmetic.MellinBogoliubovFiniteCovarianceBridge
