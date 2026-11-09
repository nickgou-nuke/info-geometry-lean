/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
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

## iii. Table of contents

1. Bipartite operators and partial trace over the second factor.
2. Trace preservation and diagonal marginal calculation.

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
