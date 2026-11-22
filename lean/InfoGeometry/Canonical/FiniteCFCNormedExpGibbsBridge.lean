/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteMatrixGibbsOperatorReadout
import InfoGeometry.Canonical.MatrixGibbsEntropy
import InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetFunctionalCalculus
import InfoGeometry.TraceFormula.OperatorialISColimitFramework

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


/-- The CFC Gibbs weight is exactly the Banach-algebra exponential. -/
theorem cfcGibbsDensity_eq_normedSpace_exp
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensity H hH β = NormedSpace.exp ((-β : ℝ) • H) := by
  exact InfoGeometry.Canonical.MatrixGibbsEntropy.gibbsDensity_eq_exp_neg_smul H hH β

theorem cfcPartition_eq_normedSpaceExpPartition
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix.trace (gibbsDensity H hH β) =
      Matrix.trace (NormedSpace.exp ((-β : ℝ) • H)) := by
  rw [cfcGibbsDensity_eq_normedSpace_exp H hH β]

noncomputable def cfcNormalizedGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) : Matrix n n ℂ :=
  (Matrix.trace (gibbsDensity H hH β))⁻¹ • gibbsDensity H hH β

noncomputable def normedExpNormalizedGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (β : ℝ) : Matrix n n ℂ :=
  (Matrix.trace (NormedSpace.exp ((-β : ℝ) • H)))⁻¹ •
    NormedSpace.exp ((-β : ℝ) • H)

theorem cfcNormalizedGibbsDensity_eq_normedExpNormalizedGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    cfcNormalizedGibbsDensity H hH β = normedExpNormalizedGibbsDensity H β := by
  unfold cfcNormalizedGibbsDensity normedExpNormalizedGibbsDensity
  rw [cfcGibbsDensity_eq_normedSpace_exp H hH β]

theorem matrixOp_cfcGibbsDensity_eq_normedSpaceExpWeight
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOp (gibbsDensity H hH β) =
      matrixOp (NormedSpace.exp ((-β : ℝ) • H)) := by
  exact congrArg matrixOp (cfcGibbsDensity_eq_normedSpace_exp H hH β)

theorem matrixOp_cfcNormalizedGibbsDensity_eq_normedExpNormalizedGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOp (cfcNormalizedGibbsDensity H hH β) =
      matrixOp (normedExpNormalizedGibbsDensity H β) := by
  exact congrArg matrixOp
    (cfcNormalizedGibbsDensity_eq_normedExpNormalizedGibbsDensity H hH β)

theorem matrixOfOp_matrixOp_cfcGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOfOp (matrixOp (gibbsDensity H hH β)) =
      NormedSpace.exp ((-β : ℝ) • H) := by
  rw [matrixOfOp_matrixOp, cfcGibbsDensity_eq_normedSpace_exp H hH β]

/-- The power-series Gibbs weight on the same finite matrix carrier. -/
def normedSpaceGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (β : ℝ) : Matrix n n ℂ :=
  NormedSpace.exp ((-β : ℝ) • H)

/-- Trace-normalized CFC Gibbs density. -/
def normalizedCFCDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) : Matrix n n ℂ :=
  cfcNormalizedGibbsDensity H hH β

/-- Trace-normalized power-series Gibbs density. -/
def normalizedNormedSpaceExpDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (β : ℝ) : Matrix n n ℂ :=
  normedExpNormalizedGibbsDensity H β

/-- The two normalized finite Gibbs states are reconciled by the equality of
their unnormalized weights. -/
theorem normalizedCFCDensity_eq_normalizedNormedSpaceExpDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    normalizedCFCDensity H hH β = normalizedNormedSpaceExpDensity H β :=
  cfcNormalizedGibbsDensity_eq_normedExpNormalizedGibbsDensity H hH β

/-- The existing normalized finite Gibbs functional can be read using the
power-series exponential without changing the state. -/
theorem gibbsFunctional_eq_normedSpaceExp_weightedTrace
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsFunctional H hH β =
      (Matrix.trace (normedSpaceGibbsDensity H β))⁻¹ •
        weightedTrace (normedSpaceGibbsDensity H β) := by
  rw [gibbsFunctional, normedSpaceGibbsDensity,
    cfcGibbsDensity_eq_normedSpace_exp H hH β]

/-- Existing bounded-operator readout of the CFC Gibbs weight, expressed using
the equal power-series matrix exponential. -/
theorem gibbsDensityOperator_eq_matrixOp_normedSpace_exp
    {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensityOperator H hH β = matrixOp (normedSpaceGibbsDensity H β) := by
  rw [gibbsDensityOperator, normedSpaceGibbsDensity,
    cfcGibbsDensity_eq_normedSpace_exp H hH β]

/-- Operator readouts of the two normalized matrix states agree. -/
theorem matrixOp_normalizedCFCDensity_eq_normedSpaceExpDensity
    {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOp (normalizedCFCDensity H hH β) =
      matrixOp (normalizedNormedSpaceExpDensity H β) :=
  matrixOp_cfcNormalizedGibbsDensity_eq_normedExpNormalizedGibbsDensity H hH β

end InfoGeometry.Canonical.FiniteCFCNormedExpGibbsBridge
