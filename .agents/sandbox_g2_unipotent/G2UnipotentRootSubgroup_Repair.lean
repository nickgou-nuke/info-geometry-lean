-- SPDX-FileCopyrightText: 2024–2026 The InfoGeometry Authors
-- SPDX-License-Identifier: MIT

/-
# Coordinatewise repair for `G2UnipotentRootSubgroup`

The original `unipotentShort_mul` and `unipotentLong_mul` proofs use `ext` + `dsimp` + `all_goals simp`
which forces Lean to expand the entire 8-coordinate Zorn multiplication formula for all
X, Y ∈ (𝔽₂)⁸ — a 2¹⁶-case elaborator explosion.

This file provides the coordinatewise definitions that enable a bounded proof.
The Boolean ring lemmas (distributivity, associativity, etc.) are available from
`Mathlib.Data.Bool.Basic` and should be used directly in the per-coordinate proofs.

The actual multiplicativity proofs in `G2UnipotentRootSubgroup.lean`
should be rewritten to use these definitions coordinate-by-coordinate:

```lean
theorem unipotentShort_mul (t : Bool) (X Y : SplitOctF2) :
    unipotentShort t (mul X Y) = mul (unipotentShort t X) (unipotentShort t Y) := by
  cases t with
  | false => rfl
  | true =>
    ext <;>
    (try decide) <;>
    (try {
      simp only [unipotentShort, mul, dot3, cross0, cross1, cross2, mul2]
      <;>
      -- Per-coordinate simp with Bool ring lemmas from Mathlib
      simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm,
        Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm,
        Bool.and_self, Bool.xor_self, Bool.and_false, Bool.and_true,
        Bool.xor_false]
      <;>
      (try decide)
    })
```

This pattern expands only one coordinate at a time and uses targeted `simp`
lemmas, keeping the elaborator state bounded.
-/

import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2UnipotentRepair

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- The unipotentShort transformation on the 8 Bool coordinates -/
def unipotentShort_coord (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, X.x0 ^^ X.x1, X.x1, X.x2, X.y0, X.y1 ^^ X.y0, X.y2⟩
  else X

/-- The unipotentLong transformation on the 8 Bool coordinates -/
def unipotentLong_coord (t : Bool) (X : SplitOctF2) : SplitOctF2 :=
  if t then
    ⟨X.a, X.b, X.x0, X.x1 ^^ X.x2, X.x2, X.y0, X.y1, X.y2 ^^ X.y1⟩
  else X

end InfoGeometry.Algebra.Zorn.G2UnipotentRepair