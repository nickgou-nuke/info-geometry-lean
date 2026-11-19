/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite bipartite matrix partial trace

## i. Overview

Defines the finite partial trace over the second tensor factor for complex
matrices indexed by products of finite ordinals. The declarations retain their
established `FiniteAttentionCanonicalBridges` namespace so existing consumers
can reuse this focused owner without importing unrelated measure-theoretic
bridges.

## ii. Key results

- `partialTraceSecondOp_trace`: the partial trace preserves total matrix trace.
- `partialTraceSecondOp_diagonal`: a diagonal bipartite operator has the
  expected diagonal marginal.
- `trace_mul_partialTraceSecondOp`: full-matrix trace adjointness for tensoring
  an observable with the second-factor identity. Its established
  `QuantumContext.MatrixStagePartialTrace` namespace is preserved.

## iii. Table of contents

1. Bipartite operators and partial trace over the second factor.
2. Trace preservation and diagonal marginal calculation.
3. Trace adjointness for arbitrary full matrix observables.

## iv. References

- M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum
  Information*, finite-dimensional partial trace.
-/

open scoped BigOperators

namespace InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

abbrev BipartiteOperator (m n : ℕ) :=
  Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ

noncomputable def partialTraceSecondOp {m n : ℕ}
    (ρ : BipartiteOperator m n) : Matrix (Fin m) (Fin m) ℂ :=
  fun i k => ∑ j, ρ (i, j) (k, j)

theorem partialTraceSecondOp_trace {m n : ℕ} (ρ : BipartiteOperator m n) :
    Matrix.trace (partialTraceSecondOp ρ) = Matrix.trace ρ := by
  simp only [Matrix.trace, Matrix.diag, partialTraceSecondOp]
  rw [Fintype.sum_prod_type]

theorem partialTraceSecondOp_diagonal {m n : ℕ}
    (p : Fin m → Fin n → ℂ) :
    partialTraceSecondOp (Matrix.diagonal (fun ij => p ij.1 ij.2)) =
      Matrix.diagonal (fun i => ∑ j, p i j) := by
  ext i k
  by_cases hik : i = k
  · subst k
    simp [partialTraceSecondOp]
  · simp [partialTraceSecondOp, hik]

end InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

namespace InfoGeometry.QuantumContext.MatrixStagePartialTrace

open scoped Kronecker
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

/-- The unnormalized full-matrix partial trace over a finite second index. -/
theorem trace_mul_partialTraceSecondOp
    {m r : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (D : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ) :
    Matrix.trace (A * partialTraceSecondOp D) =
      Matrix.trace ((A ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) * D) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    partialTraceSecondOp, Matrix.kronecker_apply, Fintype.sum_prod_type]
  simp [Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

end InfoGeometry.QuantumContext.MatrixStagePartialTrace
