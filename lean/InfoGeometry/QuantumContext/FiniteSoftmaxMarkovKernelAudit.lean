/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel

/-!
# Kernel Axiom Audit: Finite Softmax Markov Kernel

The declarations below expose the axioms used by the finite softmax,
row-stochasticity, group-inverse, and range-constrained Poisson-solver results.
-/

open InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel

#print axioms gibbsCouplingWeight_pos
#print axioms queryPartitionFunction_pos
#print axioms softmaxAttentionKernel_pos
#print axioms softmaxAttentionKernel_row_sum
#print axioms softmaxAttentionMatrix_mem_rowStochastic
#print axioms exists_softmaxAttention_laplacian_groupInverse
#print axioms softmaxAttention_poisson_solution_exists_unique
#print axioms softmaxAttention_poisson_solutions_differ_by_const
