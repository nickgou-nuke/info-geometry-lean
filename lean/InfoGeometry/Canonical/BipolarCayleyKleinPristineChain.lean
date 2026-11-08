import InfoGeometry.Algebra.Zorn.NativeGradedCochainTwist
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.QuadraticCayleyDomain
import InfoGeometry.Canonical.BipolarDiagonalBerezinianCayley

/-!
# The corrected Cayley/cochain/Berezinian chain

There are separate algebraic and analytic operations, not one operation
converting Lorentz symmetry into dissipative dynamics. The finite cochain
changes multiplication on a homogeneous frame. The scalar Cayley map changes
coordinates. The diagonal Berezinian is a character on invertible even
blocks. This capstone joins their certified identities without identifying
any of these carriers or introducing a physical evolution law.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarCayleyKleinPristineChain

open InfoGeometry.Algebra.Zorn.Z2ThreeCochainBridge
open InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation
open InfoGeometry.Algebra.Zorn.NativeGradedCochainTwist
open InfoGeometry.Algebra.Zorn.QuadraticCayleyDomain
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarCayleyOccupation
open InfoGeometry.Canonical.BipolarDiagonalBerezinianCayley

/-- The common real dimension does not imply a common multiplication. -/
theorem pristine_eight_dimensional_separation :
    Module.finrank ℝ ComplexMatrix = 8 ∧
      Module.finrank ℝ SplitCarrier = 8 ∧
      ¬ ∃ f : ComplexMatrix → SplitCarrier,
        Function.Surjective f ∧ ∀ A B, f (A * B) = f A * f B := by
  exact ⟨complexMatrix_finrank, splitCarrier_finrank,
    no_surjective_multiplicative_matrix_map⟩

/-- Exact native binary twist and its nontrivial coboundary readout. -/
theorem pristine_native_twist (x y z : Z2Grade) :
    splitGrade x * splitGrade y =
        (nativeTwist x y : ℝ) • matrixSplitLinearEquiv (matrixGrade x * matrixGrade y) ∧
      associatorCochain nativeTwist x y z = signUnit (associatorParity x y z) := by
  exact ⟨nativeTwist_product x y, by
    rw [nativeTwist_coboundary, splitCochain_associator]⟩

/-- The real rapidity chart is bounded; the complex midpoint condition remains separate. -/
theorem pristine_real_occupation (t : ℝ) :
    0 < logistic t ∧ logistic t < 1 ∧
      2 * logistic t - 1 = Real.tanh (t / 2) ∧
      logOdds (logistic t) = t := by
  exact ⟨logistic_pos t, logistic_lt_one t,
    real_polarization_eq_tanh t, logOdds_logistic t⟩

/-- Scalar reciprocity and the two genuine block-invertibility conditions. -/
theorem pristine_cayley_berezinian {s : ℂ} (hs : s ∈ punctured01)
    (hmid : s ≠ 1 / 2) :
    fugacityCayley (crossRatio01 s) = polarization s ∧
      1 + crossRatio01 s ≠ 0 ∧ 1 - crossRatio01 s ≠ 0 ∧
      fugacityBerezinianReadout (crossRatio01 s) = centeredBerezinianReadout s ∧
      (s - 1 / 2) * centeredBerezinianReadout s = -1 / 2 := by
  exact ⟨fugacityCayley_crossRatio hs,
    (diagonal_blocks_regular hs hmid).1,
    (diagonal_blocks_regular hs hmid).2,
    fugacityBerezinianReadout_crossRatio hs,
    centeredBerezinian_pole_coefficient hmid⟩

/-- On every nonzero critical-line height, polarization and the odd block are nonzero. -/
theorem pristine_critical_line_correction {y : ℝ} (hy : y ≠ 0) :
    polarization (criticalLine y) ≠ 0 ∧
      1 - crossRatio01 (criticalLine y) ≠ 0 ∧
      centeredBerezinianReadout (criticalLine y) = Complex.I / (2 * (y : ℂ)) := by
  exact ⟨fun h => hy ((criticalLine_polarization_zero_iff y).1 h),
    criticalLine_odd_block_regular hy, centeredBerezinian_criticalLine hy⟩

end InfoGeometry.Canonical.BipolarCayleyKleinPristineChain

