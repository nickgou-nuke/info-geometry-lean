/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.DyadicMatrixTraceColimit
import InfoGeometry.Categorical.MatrixAmplificationShellSymmetry

/-!
# The shell symmetry preserves the normalized colimit trace

Both owners use the same full matrix stages and the same algebraic colimit.
Trace equivariance on a fresh shell therefore gives normalized trace
invariance by induction, then invariance on the actual colimit by its
finite-stage representatives.
-/

noncomputable section

namespace InfoGeometry.Canonical.DyadicMatrixTraceShellSymmetry

open DyadicMatrixTraceColimit
open InfoGeometry.Categorical

attribute [local reducible] MatrixAmplificationTower.stage MatrixAmplificationTower.matrixFunctor

variable (K : Type) [CommRing K] [Invertible (2 : K)]

/-- Every recursively normalized stage trace is invariant under the constructed
product of fresh-shell sign conjugations. -/
@[simp]
theorem stageTrace_stageSymmetry (n : ℕ) :
    ∀ x : Stage K n,
      stageTrace K n (MatrixAmplificationShellSymmetry.stageSymmetry K n x) =
        stageTrace K n x := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      rw [stageTrace_succ_apply,
        MatrixAmplificationShellSymmetry.trace_stageSymmetry_succ,
        ih, stageTrace_succ_apply]

/-- The genuine algebraic-colimit automorphism preserves the descended
normalized linear trace. -/
@[simp]
theorem colimitTrace_colimitSymmetry (x : Carrier K) :
    colimitTrace K (MatrixAmplificationShellSymmetry.colimitSymmetry K x) =
      colimitTrace K x := by
  obtain ⟨n, a, rfl⟩ :=
    MatrixAmplificationTower.exists_stage (Fin 2) (RingCat.of K) x
  rw [MatrixAmplificationShellSymmetry.colimitSymmetry_inclusion]
  change stageTrace K n (MatrixAmplificationShellSymmetry.stageSymmetry K n a) =
    stageTrace K n a
  exact stageTrace_stageSymmetry K n a

end InfoGeometry.Canonical.DyadicMatrixTraceShellSymmetry
