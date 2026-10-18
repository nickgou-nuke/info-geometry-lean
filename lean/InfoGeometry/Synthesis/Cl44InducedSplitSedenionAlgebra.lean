/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge

/-!
# Transported split-sedenion operations on the matrix-model principal ideal

These definitions transport the split-sedenion pair operations through the carrier
equivalence. They do not identify the transported product with matrix multiplication.
The module-structure and bilinearity results are proved in
`Cl44MinimalIdealInducedSedenionProductBridge`.
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.Cl44InducedSplitSedenionAlgebra

open InfoGeometry.Cl44IdempotentIdeal
open InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis

/-- Split-sedenion multiplication transported to `LeftIdeal primIdem`. -/
def idealSedenionMul (A B : LeftIdeal primIdem) : LeftIdeal primIdem :=
  cl44MatrixLeftIdealSplitSedenionEquiv.symm
    (sedenionMul (cl44MatrixLeftIdealSplitSedenionEquiv A)
      (cl44MatrixLeftIdealSplitSedenionEquiv B))

/-- Cayley–Dickson conjugation transported to `LeftIdeal primIdem`. -/
def idealSedenionConj (A : LeftIdeal primIdem) : LeftIdeal primIdem :=
  cl44MatrixLeftIdealSplitSedenionEquiv.symm
    (sedenionConj (cl44MatrixLeftIdealSplitSedenionEquiv A))

/-- The split-sedenion quadratic expression transported to `LeftIdeal primIdem`. -/
def idealSedenionNorm (A : LeftIdeal primIdem) : ℝ :=
  sedenionNorm (cl44MatrixLeftIdealSplitSedenionEquiv A)

end InfoGeometry.Synthesis.Cl44InducedSplitSedenionAlgebra
