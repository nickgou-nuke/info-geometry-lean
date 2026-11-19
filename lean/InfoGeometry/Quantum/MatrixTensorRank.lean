/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic

/-!
# Rank of full matrix tensor products

## Overview

The range of a tensor product of linear maps is the tensor product of their
ranges, embedded by the native injective tensor inclusion over a field.
Its dimension therefore multiplies. Native tensor-product bases transport
this statement to full matrix Kronecker products without restricting entries
or replacing multiplication by a commuting model.

## Key results

- `finrank_range_tensorProductMap`: dimensions of tensor-map ranges multiply.
- `rank_kronecker`: ranks of full square matrix Kronecker products multiply.

## Table of contents

1. Tensor-map ranges.
2. Matrix Kronecker rank.

## References

The proof uses Mathlib's tensor inclusion, flatness over a field, tensor
bases, and basis-independent matrix rank.
-/

noncomputable section

namespace InfoGeometry.Quantum.MatrixTensorRank

open scoped TensorProduct Kronecker

/-- The range dimension of an actual tensor product of linear maps. -/
theorem finrank_range_tensorProductMap
    {𝕜 E F E' F' : Type*} [Field 𝕜]
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup E'] [AddCommGroup F']
    [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 E'] [Module 𝕜 F']
    (f : E →ₗ[𝕜] E') (g : F →ₗ[𝕜] F') :
    Module.finrank 𝕜 (LinearMap.range (TensorProduct.map f g)) =
      Module.finrank 𝕜 (LinearMap.range f) *
        Module.finrank 𝕜 (LinearMap.range g) := by
  calc
    Module.finrank 𝕜 (LinearMap.range (TensorProduct.map f g)) =
        Module.finrank 𝕜 (LinearMap.range
          (TensorProduct.mapIncl (LinearMap.range f) (LinearMap.range g))) := by
      rw [TensorProduct.range_map, TensorProduct.range_mapIncl]
    _ = Module.finrank 𝕜 ((LinearMap.range f) ⊗[𝕜] (LinearMap.range g)) :=
      LinearMap.finrank_range_of_inj
        (Module.Flat.tensorProduct_mapIncl_injective_of_right
          (LinearMap.range f) (LinearMap.range g))
    _ = _ := by rw [Module.finrank_tensorProduct]

/-- Exact rank multiplication for full square matrices over any field. -/
theorem rank_kronecker {𝕜 m n : Type*} [Field 𝕜]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  let bm := Pi.basisFun 𝕜 m
  let bn := Pi.basisFun 𝕜 n
  rw [Matrix.rank_eq_finrank_range_toLin (A ⊗ₖ B)
      (bm.tensorProduct bn) (bm.tensorProduct bn),
    Matrix.toLin_kronecker, finrank_range_tensorProductMap,
    ← Matrix.rank_eq_finrank_range_toLin A bm bm,
    ← Matrix.rank_eq_finrank_range_toLin B bn bn]

end InfoGeometry.Quantum.MatrixTensorRank
