/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.QuantumContext.MarkovGroupInversePetzSupport

/-!
# A non-orthogonal Markov group-inverse projector

This finite full-matrix example records why a group-inverse range idempotent
must not be identified with an orthogonal density-support projection without
additional hypotheses. The transition is strictly positive and stochastic;
its Laplacian has a group inverse, while the induced range idempotent is not
self-adjoint under matrix transpose. The ambient carrier remains the full
noncommutative matrix algebra.
-/

namespace InfoGeometry.QuantumContext.MarkovObliqueSupportWitness

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-- A strictly positive row-stochastic transition matrix on two states. -/
noncomputable def transition : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then (if j = 0 then (3 : ℝ) / 4 else 1 / 4)
    else 1 / 2

/-- The explicit group inverse of `1 - transition`. -/
noncomputable def laplacianGroupInverse : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then (if j = 0 then (4 : ℝ) / 9 else -(4 / 9 : ℝ))
    else (if j = 0 then -(8 / 9 : ℝ) else 8 / 9)

/-- The transition has nonnegative entries and row sums equal to one. -/
theorem transition_rowStochastic :
    transition ∈ Matrix.rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [transition]
  · intro i
    fin_cases i <;> norm_num [transition, Fin.sum_univ_two]

/-- Every transition entry is strictly positive. -/
theorem transition_entrywise_pos (i j : Fin 2) : 0 < transition i j := by
  fin_cases i <;> fin_cases j <;> norm_num [transition]

/-- The exhibited matrix is a group inverse for the Markov Laplacian. -/
theorem laplacianGroupInverse_isGroupInverse :
    IsGroupInverse (1 - transition) laplacianGroupInverse := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [transition, laplacianGroupInverse, Matrix.mul_apply,
        Matrix.one_apply, Fin.sum_univ_succ]
  · constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [transition, laplacianGroupInverse, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_succ]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [transition, laplacianGroupInverse, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_succ]

/-- The group-inverse range idempotent has explicit nonsymmetric entries. -/
theorem rangeIdempotent_eq :
    markovRangeIdempotent transition laplacianGroupInverse =
      !![(1 : ℝ) / 3, -(1 / 3 : ℝ);
         -(2 / 3 : ℝ), 2 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [markovRangeIdempotent, transition, laplacianGroupInverse,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- The concrete matrix representing the Markov range idempotent. -/
noncomputable def rangeIdempotent : Matrix (Fin 2) (Fin 2) ℝ :=
  markovRangeIdempotent transition laplacianGroupInverse

/-- This valid group-inverse range idempotent is not self-adjoint. -/
theorem rangeIdempotent_not_symmetric :
    Matrix.transpose (markovRangeIdempotent transition laplacianGroupInverse) ≠
      markovRangeIdempotent transition laplacianGroupInverse := by
  rw [rangeIdempotent_eq]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num at h01

/-- The complement is likewise not an orthogonal projection under transpose. -/
theorem stationaryProjector_not_symmetric :
    Matrix.transpose (1 - markovRangeIdempotent transition laplacianGroupInverse) ≠
      1 - markovRangeIdempotent transition laplacianGroupInverse := by
  rw [rangeIdempotent_eq]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num at h01

/-- The Markov range idempotent is not central in the full matrix algebra:
it fails to commute with a matrix unit. This ties the obliqueness witness to
the noncommutative operator carrier rather than merely asserting that the
ambient carrier is noncommutative. -/
def matrixUnit01 : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; 0, 0]

/-- Explicit noncommutation in the full real matrix carrier, witnessed by the
Markov range idempotent and the `(0,1)` matrix unit. -/
theorem rangeIdempotent_mul_matrixUnit01_ne :
    rangeIdempotent * matrixUnit01 ≠ matrixUnit01 * rangeIdempotent := by
  change markovRangeIdempotent transition laplacianGroupInverse * matrixUnit01 ≠
    matrixUnit01 * markovRangeIdempotent transition laplacianGroupInverse
  rw [rangeIdempotent_eq]
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [matrixUnit01, Matrix.mul_apply, Fin.sum_univ_succ] at h00

theorem rangeIdempotent_not_central :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      markovRangeIdempotent transition laplacianGroupInverse * X ≠
        X * markovRangeIdempotent transition laplacianGroupInverse := by
  exact ⟨matrixUnit01, rangeIdempotent_mul_matrixUnit01_ne⟩

end InfoGeometry.QuantumContext.MarkovObliqueSupportWitness
