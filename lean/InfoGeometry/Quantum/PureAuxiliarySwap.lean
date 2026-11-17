/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.FinitePartialTrace
import InfoGeometry.Quantum.ChoiCompletePositivity
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Exact finite erasure using a pure auxiliary system

## Overview

The native permutation matrix of the coordinate swap is a genuine joint
unitary. Its conjugation exchanges arbitrary full matrix tensor factors.
Consequently, a system operator of trace one can be replaced by any prescribed
normalized pure state by swapping it with an auxiliary system in that state.

This records the boundary of the faithful-bath rank obstruction: the pure
auxiliary state is an additional resource. No work, preparation cost, or
temperature claim is inferred.

## Key results

- `swap_conjugate_kronecker`: ordered conjugation exchanges full matrix factors.
- `exists_unitary_swap_product`: the conjugating matrix belongs to the native
  unitary group, using the existing permutation-unitarity theorem.
- `exists_unitary_erasure_with_pure_auxiliary`: actual partial-trace erasure,
  together with positivity, trace one, and projection purity of the auxiliary.

## Table of contents

1. Full matrix SWAP conjugation.
2. Native unitary witness.
3. Normalized pure auxiliary and actual reduced state.

## References

The proof reuses Mathlib permutation-matrix multiplication and the repository's
finite partial trace and `Quantum.Choi.permutationMatrix_unitary`.
-/

noncomputable section

namespace InfoGeometry.Quantum.PureAuxiliarySwap

open Matrix
open scoped ComplexOrder Kronecker
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges

/-- The permutation matrix acts on both actual tensor indices, retaining all
entries of both factors and the ordered matrix multiplication. -/
theorem swap_conjugate_kronecker {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (Equiv.prodComm (Fin n) (Fin n)).permMatrix ℂ * (A ⊗ₖ B) *
      star ((Equiv.prodComm (Fin n) (Fin n)).permMatrix ℂ) = B ⊗ₖ A := by
  let e : Equiv.Perm (Fin n × Fin n) := Equiv.prodComm (Fin n) (Fin n)
  change e.permMatrix ℂ * (A ⊗ₖ B) * (e.permMatrix ℂ)ᴴ = B ⊗ₖ A
  rw [Matrix.conjTranspose_permMatrix]
  change e.toPEquiv.toMatrix * (A ⊗ₖ B) * (e⁻¹).toPEquiv.toMatrix = B ⊗ₖ A
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext ⟨i, j⟩ ⟨k, l⟩
  change A j l * B i k = B i k * A j l
  exact mul_comm _ _

/-- The SWAP witness is a member of the native unitary group. -/
theorem exists_unitary_swap_product {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : unitary (BipartiteOperator n n),
      (U : BipartiteOperator n n) * (A ⊗ₖ B) * star (U : BipartiteOperator n n) =
        B ⊗ₖ A := by
  let e : Equiv.Perm (Fin n × Fin n) := Equiv.prodComm (Fin n) (Fin n)
  have hu := InfoGeometry.Quantum.Choi.permutationMatrix_unitary e
  let U : unitary (BipartiteOperator n n) := ⟨e.permMatrix ℂ, hu.2, hu.1⟩
  refine ⟨U, ?_⟩
  exact swap_conjugate_kronecker A B

/-- Every normalized pure target is reachable with a same-dimension pure
auxiliary. The construction applies in particular to arbitrary positive
trace-one system densities; positivity of the input is unnecessary for this
stronger exact partial-trace identity. -/
theorem exists_unitary_erasure_with_pure_auxiliary {n : ℕ}
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : Matrix.trace ρ = 1)
    (v : Fin n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    ∃ U : unitary (BipartiteOperator n n),
      (Matrix.vecMulVec v (star v)).PosSemidef ∧
      Matrix.trace (Matrix.vecMulVec v (star v)) = 1 ∧
      IsStarProjection (Matrix.vecMulVec v (star v)) ∧
      partialTraceSecondOp ((U : BipartiteOperator n n) *
        (ρ ⊗ₖ Matrix.vecMulVec v (star v)) * star (U : BipartiteOperator n n)) =
          Matrix.vecMulVec v (star v) := by
  obtain ⟨U, hU⟩ := exists_unitary_swap_product ρ (Matrix.vecMulVec v (star v))
  refine ⟨U, Matrix.posSemidef_vecMulVec_self_star v, ?_, ?_, ?_⟩
  · calc
      Matrix.trace (Matrix.vecMulVec v (star v)) = v ⬝ᵥ star v := Matrix.trace_vecMulVec _ _
      _ = star v ⬝ᵥ v := dotProduct_comm _ _
      _ = 1 := hv
  · refine ⟨?_, (Matrix.posSemidef_vecMulVec_self_star v).isHermitian⟩
    change Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) = _
    rw [Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]
  · rw [hU]
    ext i j
    change (∑ k, Matrix.vecMulVec v (star v) i j * ρ k k) = Matrix.vecMulVec v (star v) i j
    rw [← Finset.mul_sum]
    change Matrix.vecMulVec v (star v) i j * Matrix.trace ρ = _
    rw [hρ, mul_one]

end InfoGeometry.Quantum.PureAuxiliarySwap
