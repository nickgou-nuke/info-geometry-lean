/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Prototype: finite Markov row laws

This scratch file checks the first probability bridge needed to interpret the
finite-horizon Bellman iterates: each row of a real row-stochastic matrix is a
finite probability mass function. It does not yet construct path laws or prove
an expected hitting-time identity.
-/

namespace InfoGeometry.QuantumContext.FiniteMarkovPathExpectationPrototype

open Matrix ProbabilityTheory
open MeasureTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability mass function given by one row of a row-stochastic matrix. -/
noncomputable def rowPMF (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) : PMF ι :=
  PMF.ofFintype (fun j => ENNReal.ofReal (P i j)) (by
    calc
      (∑ j, ENNReal.ofReal (P i j)) =
          ENNReal.ofReal (∑ j, P i j) := by
            symm
            apply ENNReal.ofReal_sum_of_nonneg
            intro j hj
            exact Matrix.nonneg_of_mem_rowStochastic hP
      _ = 1 := by rw [Matrix.sum_row_of_mem_rowStochastic hP i]; norm_num)

@[simp]
theorem rowPMF_apply (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i j : ι) :
    rowPMF P hP i j = ENNReal.ofReal (P i j) := by
  simp [rowPMF]

/-- The associated measure assigns each singleton its transition probability. -/
theorem rowPMF_toMeasure_singleton (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i j : ι)
    [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    (rowPMF P hP i).toMeasure {j} = ENNReal.ofReal (P i j) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
  exact rowPMF_apply P hP i j

/-- The row measure is a probability measure. -/
theorem rowPMF_toMeasure_isProbabilityMeasure (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) [MeasurableSpace ι] :
    IsProbabilityMeasure (rowPMF P hP i).toMeasure := by
  infer_instance

/-- A one-step expectation under the row law is exactly matrix-vector action. -/
theorem rowPMF_integral_eq_mulVec (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι)
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (x : ι → ℝ) :
    ∫ j, x j ∂(rowPMF P hP i).toMeasure = (P.mulVec x) i := by
  rw [PMF.integral_eq_sum]
  simp [Matrix.mulVec, dotProduct, rowPMF_apply, ENNReal.toReal_ofReal,
    Matrix.nonneg_of_mem_rowStochastic hP]

end InfoGeometry.QuantumContext.FiniteMarkovPathExpectationPrototype
