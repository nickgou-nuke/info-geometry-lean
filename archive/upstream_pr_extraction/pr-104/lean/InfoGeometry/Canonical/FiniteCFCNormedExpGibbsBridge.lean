import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

import InfoGeometry.Canonical.FiniteMatrixGibbsOperatorReadout

/-!
# CFC and Banach-exponential finite Gibbs bridge

The finite Gibbs owner defines the unnormalized weight by the Hermitian
continuous functional calculus.  This file identifies that weight with
Mathlib's power-series exponential on the same matrix carrier and transports
the resulting equalities through the existing `matrixOp` readout.

This is a finite carrier/readout theorem.  It does not turn a scalar inverse
temperature into the repository's primary operatorial Souriau beta, and it
does not assert an infinite-dimensional Araki/KMS theorem.
-/

noncomputable section

open Matrix

namespace InfoGeometry.Canonical.FiniteCFCNormedExpGibbsBridge

open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Canonical.FiniteMatrixGibbsOperatorReadout
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-- The power-series Gibbs weight on the same finite matrix carrier. -/
def normedSpaceGibbsDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (β : ℝ) : Matrix n n ℂ :=
  NormedSpace.exp ((-β : ℝ) • H)

/-- Mathlib's Hermitian CFC exponential and Banach-algebra exponential define
the same finite Gibbs weight. -/
theorem cfcGibbsDensity_eq_normedSpace_exp
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensity H hH β = normedSpaceGibbsDensity H β := by
  rw [gibbsDensity, ← hH.cfc_eq]
  change
    cfc (fun r : ℝ => Real.exp ((-β : ℝ) • r)) H =
      NormedSpace.exp ((-β : ℝ) • H)
  rw [cfc_comp_smul, CFC.real_exp_eq_normedSpace_exp]

/-- Trace-normalized CFC Gibbs density. -/
def normalizedCFCDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix n n ℂ :=
  (Matrix.trace (gibbsDensity H hH β))⁻¹ • gibbsDensity H hH β

/-- Trace-normalized power-series Gibbs density. -/
def normalizedNormedSpaceExpDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (β : ℝ) : Matrix n n ℂ :=
  (Matrix.trace (normedSpaceGibbsDensity H β))⁻¹ •
    normedSpaceGibbsDensity H β

/-- The two normalized finite Gibbs states are definitionally reconciled by
the equality of their unnormalized weights. -/
theorem normalizedCFCDensity_eq_normalizedNormedSpaceExpDensity
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    normalizedCFCDensity H hH β =
      normalizedNormedSpaceExpDensity H β := by
  rw [normalizedCFCDensity, normalizedNormedSpaceExpDensity,
    cfcGibbsDensity_eq_normedSpace_exp H hH β]

/-- The existing normalized finite Gibbs functional can be read using the
power-series exponential without changing the state. -/
theorem gibbsFunctional_eq_normedSpaceExp_weightedTrace
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsFunctional H hH β =
      (Matrix.trace (normedSpaceGibbsDensity H β))⁻¹ •
        weightedTrace (normedSpaceGibbsDensity H β) := by
  rw [gibbsFunctional, cfcGibbsDensity_eq_normedSpace_exp H hH β]

/-- Existing bounded-operator readout of the CFC Gibbs weight, expressed using
the equal power-series matrix exponential.  This theorem transports an already
proved matrix equality; it does not claim that `matrixOp` has yet been bundled
as an exponential-preserving continuous algebra equivalence. -/
theorem gibbsDensityOperator_eq_matrixOp_normedSpace_exp
    {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensityOperator H hH β =
      matrixOp (normedSpaceGibbsDensity H β) := by
  rw [gibbsDensityOperator,
    cfcGibbsDensity_eq_normedSpace_exp H hH β]

/-- Operator readouts of the two normalized matrix states agree. -/
theorem matrixOp_normalizedCFCDensity_eq_normedSpaceExpDensity
    {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    matrixOp (normalizedCFCDensity H hH β) =
      matrixOp (normalizedNormedSpaceExpDensity H β) := by
  exact congrArg matrixOp
    (normalizedCFCDensity_eq_normalizedNormedSpaceExpDensity H hH β)

end InfoGeometry.Canonical.FiniteCFCNormedExpGibbsBridge
