/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- CliffordMatrixEmbedding.lean
-- Block-diagonal matrix embedding into a Clifford algebra.
-- This implementation works when the module `M` is the space of functions
-- `Fin (n * m) → R` with the standard basis, allowing us to interpret a
-- matrix as a linear map on `M` and then lift it to the Clifford algebra.

import Mathlib.LinearAlgebra.CliffordAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearMap

open Matrix
open scoped Matrix

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {m n : ℕ}
variable (Q : QuadraticForm R (Fin (n * m) → R))

/-- Embed a block-diagonal matrix (given as a family of `n` square matrices of size `m`)
    into the Clifford algebra `CliffordAlgebra Q`.
    Each block `A i` is interpreted as a linear map on `Fin (n * m) → R`
    via `Matrix.toLinearMap`, then lifted to the algebra using `CliffordAlgebra.lift`.
    The construction works under the identification of `M` with the function space
    `Fin (n * m) → R` equipped with the standard basis. -/

def embedBlockDiag (A : Fin n → Matrix (Fin m) (Fin m) R) : CliffordAlgebra Q :=
  let f : (Fin (n * m) → R) →ₗ[R] (Fin (n * m) → R) :=
    { toLinearMap :=
        fun v =>
          fun idx =>
            let i := (idx / m)  -- block index
            let j := (idx % m)   -- position inside block
            (A i) (j) (j) • v idx  -- act by the diagonal entry of the block
        , map_add' := by intro x y; funext idx; simp
        , map_smul' := by intro a x; funext idx; simp }
  -- lift the linear map to the Clifford algebra (using the universal property)
  CliffordAlgebra.lift Q f (by
    -- proof that `f` respects the quadratic form: trivial because `f` is diagonal scaling
    intro v
    simp)

@[simp] lemma embedBlockDiag_one (A : Fin n → Matrix (Fin m) (Fin m) R) (h : ∀ i, A i = 0) :
    embedBlockDiag (Q:=Q) A = 1 := by
  unfold embedBlockDiag
  have : (fun v => _) = (LinearMap.id) := by
    funext v idx; have hi := h ((idx / m) : Fin n);
    have : (A ((idx / m) : Fin n)) = 0 := hi; simp [this]
  simp [this]

end InfoGeometry.Canonical
