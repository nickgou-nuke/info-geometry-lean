/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import OAI.CategoryTheory.Globular.Main
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# A counterexample to the direct Peirce-source globularity equation

OAI globular sets require `source (source x) = source (target x)` in each
dimension. The Peirce operators `globSource` and `globTarget` in the Tetraktys
owner instead satisfy a square-zero boundary calculus. This file gives a
finite matrix counterexample to identifying those operators directly as the
source and target on a constant carrier.

The result rules out that particular identification. It does not rule out a
different carrier, a restricted subobject, or another interpretation map.

## i. Overview

The theorem compares the exact equations required by OAI's `GlobularSet` with
the named Peirce operators on one finite matrix carrier. Its witness is a
counterexample to the direct constant-carrier proposal only.

## ii. Key results

- `peirce_source_fails_globularity_on_mat2` (`BUCKET 1`): the source-source
  equation fails for explicit `2 × 2` integer matrices.

## iii. Table of contents

- `Mat₂(ℤ)` witness for the source globularity equation.

## iv. References

- `OAI.CategoryTheory.Globular.Model.GlobularSet`
- `InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys.globSource`
- `InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys.globTarget`
-/

namespace InfoGeometry.Canonical.PeirceGlobularityComparison

open InfoGeometry.OperatorAlgebra.PeirceSpine

private def witnessP : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
private def witnessG : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
private def witnessX : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- The Peirce source maps fail the source-source globularity equation on
`Mat₂(ℤ)` for `P = E₁₁`, `g = E₁₂`, and `X = E₂₁`. -/
theorem peirce_source_fails_globularity_on_mat2 :
    globSource witnessP witnessG (globSource witnessP witnessG witnessX) ≠
      globSource witnessP witnessG (globTarget witnessP witnessG witnessX) := by
  decide

end InfoGeometry.Canonical.PeirceGlobularityComparison
