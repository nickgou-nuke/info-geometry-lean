import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteMatrixGibbsOperatorReadout

/-!
# Canonical finite CFC Gibbs readout

The finite matrix Gibbs owner uses the Hermitian continuous functional
calculus.  On the pinned Mathlib carrier there is no `NormedRing` instance
for square matrices, so this owner deliberately does not assert a
power-series exponential identity.  It records the native CFC formula and
its operator readout.
-/

noncomputable section
open Matrix

namespace InfoGeometry.Canonical.FiniteCFCNormedExpGibbsBridge

open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Canonical.FiniteMatrixGibbsOperatorReadout
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

theorem gibbsDensity_eq_cfc_expWeight
    {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensity H hH β = hH.cfc (expWeight β) := rfl

theorem gibbsDensityOperator_eq_matrixOp_cfc_expWeight
    {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensityOperator H hH β = matrixOp (hH.cfc (expWeight β)) := rfl

theorem normalizedCFCDensity_readout
    {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOp ((Matrix.trace (gibbsDensity H hH β))⁻¹ •
      gibbsDensity H hH β) =
      matrixOp ((Matrix.trace (hH.cfc (expWeight β)))⁻¹ •
        hH.cfc (expWeight β)) := by
  rfl

end InfoGeometry.Canonical.FiniteCFCNormedExpGibbsBridge
