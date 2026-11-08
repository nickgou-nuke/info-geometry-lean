/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.Abel

/-!
# The Pure Spinor Continuum Colimit and Direct-Limit Klein Twist Transport

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Constructs the categorical direct limit `ContinuumSpace M bonding = Module.DirectLimit M bonding`
    of a directed system of $R$-modules `(M i, bonding i j hij)` together with its exterior-algebra
    unit `continuumVacuum` and stage injections `continuumOf`.
- BUCKET 2 (Colimit Operations & Stage Compatibility):
  * Defines the continuum translation `continuumTranslation` and reflection `continuumReflection`
    directly as functions on `ContinuumSpace M bonding` and relates them to finite stages via
    the canonical linear map `Module.DirectLimit.of`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `continuumReflection_involutive`: reflection on `ContinuumSpace M bonding` is an involution.
  * `continuum_klein_twist_defect`: non-orientable Klein reflection-translation commutator defect
    `continuumReflection (continuumTranslation lambda x) - continuumTranslation lambda (continuumReflection x) = -(2 • lambda)`.
  * `continuum_klein_twist_defect_of_stage`: compatibility of the continuum Klein twist defect
    with the canonical colimit injection `continuumOf i : M i →ₗ[R] ContinuumSpace M bonding`.
-/

namespace InfoGeometry.GrandUnification.Continuum

variable {R ι : Type*} [CommRing R]
variable [Preorder ι] [DecidableEq ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (bonding : ∀ i j, i ≤ j → M i →ₗ[R] M j)

/-- The categorical inductive direct limit of the finite kinematic module layers. -/
abbrev ContinuumSpace : Type _ :=
  Module.DirectLimit M (fun i j h => bonding i j h)

/-- Canonical linear injection from finite stage `i` into the direct-limit continuum module. -/
noncomputable def continuumOf (i : ι) : M i →ₗ[R] ContinuumSpace M bonding :=
  Module.DirectLimit.of R ι M (fun i j h => bonding i j h) i

/-- The grade-0 unit in the exterior algebra over the direct-limit continuum module. -/
noncomputable def continuumVacuum : ExteriorAlgebra R (ContinuumSpace M bonding) :=
  1

/-- Continuum translation by `lambda` on `ContinuumSpace M bonding`. -/
noncomputable def continuumTranslation (lambda x : ContinuumSpace M bonding) : ContinuumSpace M bonding :=
  x + lambda

/-- Continuum reflection (orientation reversal) on `ContinuumSpace M bonding`. -/
noncomputable def continuumReflection (x : ContinuumSpace M bonding) : ContinuumSpace M bonding :=
  -x

/-- Continuum reflection is an involution on `ContinuumSpace M bonding`. -/
theorem continuumReflection_involutive (x : ContinuumSpace M bonding) :
    continuumReflection M bonding (continuumReflection M bonding x) = x := by
  unfold continuumReflection
  rw [neg_neg]

/-- Non-orientable Klein twist defect on the direct-limit module `ContinuumSpace M bonding`:
reversing orientation before and after translation by `lambda` yields `-(2 • lambda)`. -/
theorem continuum_klein_twist_defect (x lambda : ContinuumSpace M bonding) :
    continuumReflection M bonding (continuumTranslation M bonding lambda x) -
      continuumTranslation M bonding lambda (continuumReflection M bonding x) =
      -(2 • lambda) := by
  unfold continuumReflection continuumTranslation
  have h1 : -(x + lambda) - (-x + lambda) = -(lambda + lambda) := by abel
  rw [h1, two_smul]

/-- Stage-to-colimit compatibility: the continuum Klein twist defect on images of stage `i`
equals the canonical colimit injection of the stage-`i` defect `-(2 • lambda)`. -/
theorem continuum_klein_twist_defect_of_stage (i : ι) (x lambda : M i) :
    continuumReflection M bonding
        (continuumTranslation M bonding (continuumOf M bonding i lambda) (continuumOf M bonding i x)) -
      continuumTranslation M bonding (continuumOf M bonding i lambda)
        (continuumReflection M bonding (continuumOf M bonding i x)) =
      continuumOf M bonding i (-(2 • lambda)) := by
  rw [continuum_klein_twist_defect M bonding (continuumOf M bonding i x) (continuumOf M bonding i lambda)]
  rw [map_neg, map_nsmul]

end InfoGeometry.GrandUnification.Continuum
