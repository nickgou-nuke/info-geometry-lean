/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# Zorn Braid Colimit Continuum

This file defines the infinite-dimensional colimit for the finite Zorn seed
and $S_3$ braid color extensions using strict Mathlib CategoryTheory limits.
Following the Colimit Continuum Mandate, we do not use set-theoretic unions or
analytical continuations.

Because Zorn coordinates (split-octonions) are non-associative, they cannot be
modeled in `RingCat` or `AlgebraCat` natively. Instead, we model the finite
algebraic stages as a filtered functor `F : J ⥤ ModuleCat R` and define the
continuum carrier as `colimit F`.

The generic multiplication layer remains conditional because a family of
stagewise bilinear maps alone does not imply compatibility with the bonding
maps. This file packages the resulting operation only when that compatibility
and descent have been supplied. The concrete sequential Zorn tower proves the
bonding compatibility and performs the two tensor-colimit descents natively in
`InfoGeometry.Categorical.ZornUHFColimit`; its `colimit_mul_ι_same_stage`
theorem is the finite-stage readback authority.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `zorn_continuum_module`: The universal continuous module built from finite stages.
  - `zorn_scaling_covariance_colimit`: Scaling covariance maps naturally to the continuum.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES**:
  - `CompatibleBilinearMultiplication`: explicit witness for descended bilinear
    multiplication on the colimit.
  - `colimit_square_zero_of_stage`: finite square-zero relations transport
    through the witnessed colimit multiplication.
- **BUCKET 3: GENERIC CLOSURE DEBT**:
  - Replace this compatibility wrapper for arbitrary filtered index categories
    by explicit bonding naturality and a generic two-variable tensor descent.
  - The concrete sequential Zorn tower is already closed in `ZornUHFColimit`.
-/

namespace InfoGeometry.Categorical.ZornBraidColimit

open CategoryTheory
open CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R]
variable {J : Type u} [Category.{u} J]

-- The directed diagram representing the finite tower of Zorn vector spaces over R.
variable (ZornSequence : J ⥤ ModuleCat.{u} R)

/--
The infinite-dimensional continuous Zorn limit is exactly the
categorical direct colimit of the finite Zorn sequence in ModuleCat.
-/
noncomputable def zornContinuumModule [HasColimit ZornSequence] : ModuleCat.{u} R :=
  colimit ZornSequence

/-! ## Witnessed bilinear multiplication on the colimit -/

/--
Explicit data saying that finite-stage bilinear multiplications have descended
through the `ModuleCat` colimit.

The field `colimitMul_ι_ι` is the theorem-safe compatibility law: multiplying
two elements after inserting them into the colimit agrees with inserting their
finite-stage product. This avoids pretending that the tensor/filtered-colimit
descent theorem has already been instantiated for a concrete Zorn tower.
-/
structure CompatibleBilinearMultiplication
    [HasColimit ZornSequence] where
  /-- Finite-stage bilinear multiplication. -/
  stageMul : ∀ j : J, ZornSequence.obj j →ₗ[R] ZornSequence.obj j →ₗ[R] ZornSequence.obj j
  /-- Descended bilinear multiplication on the colimit carrier. -/
  colimitMul : ↑(colimit ZornSequence) →ₗ[R]
    ↑(colimit ZornSequence) →ₗ[R] ↑(colimit ZornSequence)
  /-- Compatibility with the finite-stage colimit injections. -/
  colimitMul_ι_ι : ∀ (j : J) (x y : ZornSequence.obj j),
    colimitMul ((colimit.ι ZornSequence j) x) ((colimit.ι ZornSequence j) y) =
      (colimit.ι ZornSequence j) (stageMul j x y)

namespace CompatibleBilinearMultiplication

variable [HasColimit ZornSequence]
variable (M : CompatibleBilinearMultiplication R ZornSequence)

/-- The witnessed multiplication agrees with finite-stage multiplication on colimit images. -/
theorem mul_colimit_ι_ι (j : J) (x y : ZornSequence.obj j) :
    M.colimitMul ((colimit.ι ZornSequence j) x) ((colimit.ι ZornSequence j) y) =
      (colimit.ι ZornSequence j) (M.stageMul j x y) :=
  M.colimitMul_ι_ι j x y

/--
A square-zero finite-stage seed remains square-zero after insertion into the
categorical `ModuleCat` colimit, provided a compatible descended multiplication
has been supplied.
-/
theorem colimit_square_zero_of_stage {j : J} {x : ZornSequence.obj j}
    (h : M.stageMul j x x = 0) :
    M.colimitMul ((colimit.ι ZornSequence j) x) ((colimit.ι ZornSequence j) x) = 0 := by
  rw [M.colimitMul_ι_ι]
  rw [h]
  simp

end CompatibleBilinearMultiplication

-- Functor representing a scaled version of the Zorn stages.
variable (ZornSequenceScaled : J ⥤ ModuleCat.{u} R)

-- Finite scaling covariance provides a natural isomorphism between
-- the standard Zorn stages and the scaled Zorn stages.
variable (zorn_scaling_covariance : ZornSequence ≅ ZornSequenceScaled)

/--
The scaling covariance naturally extends to the continuum colimit via
the universal property of the limit in ModuleCat.
-/
noncomputable def zorn_scaling_covariance_colimit
    [HasColimit ZornSequence] [HasColimit ZornSequenceScaled] :
    zornContinuumModule R ZornSequence ≅ zornContinuumModule R ZornSequenceScaled :=
  HasColimit.isoOfNatIso zorn_scaling_covariance

/--
Tensoring with a fixed `ModuleCat` object preserves colimits in `ModuleCat`.

This is the categorical fact needed for the `ModuleCat` projection path: a
bilinear multiplication can be transported through filtered colimits by fixing
one tensor factor and invoking the colimit-preservation instance.
-/
theorem moduleCat_tensorLeft_preservesColimits (A : ModuleCat.{u} R) :
    Limits.PreservesColimits (CategoryTheory.MonoidalCategory.tensorLeft A) := by
  infer_instance

/--
The colimit of a tensor-left diagram is canonically isomorphic to tensoring
the colimit by the fixed module.

This is the precise `ModuleCat` comparison iso used when the tower
multiplication is expressed as a bilinear map.
-/
noncomputable def tensorLeftColimitIso
    (A : ModuleCat.{u} R) (F : J ⥤ ModuleCat.{u} R) [HasColimit F] :
    (CategoryTheory.MonoidalCategory.tensorLeft A).obj (colimit F) ≅
      colimit (F ⋙ CategoryTheory.MonoidalCategory.tensorLeft A) := by
  have hcol :
      IsColimit ((CategoryTheory.MonoidalCategory.tensorLeft A).mapCocone
        (colimit.cocone F)) := by
    simpa using
      (isColimitOfPreserves (F := CategoryTheory.MonoidalCategory.tensorLeft A)
        (colimit.isColimit F))
  exact
    IsColimit.coconePointUniqueUpToIso hcol
      (colimit.isColimit (F := F ⋙ CategoryTheory.MonoidalCategory.tensorLeft A))

/-!
## On-shell nilpotent seeds at the categorical colimit boundary

Following the Colimit Continuum Mandate, this section projects finite
square-zero seed elements into the `ModuleCat` colimit.  The result is stated
relative to a `CompatibleBilinearMultiplication` witness; it does not install an
unproved global nonassociative algebra instance on the colimit.
-/

variable [HasColimit ZornSequence]
variable (M : CompatibleBilinearMultiplication R ZornSequence)

-- A sequence of finite-stage on-shell/nilpotent seed generators.
variable (zornCuntzGenerator : ∀ j, ZornSequence.obj j)

/--
The colimit image of a finite nilpotent seed.  The name records the intended
Cuntz/on-shell use case, while the theorem below only asserts the proved
square-zero algebraic fact supplied by the witness `M`.
-/
noncomputable def continuumCuntzGenerator (j : J) : ↑(zornContinuumModule R ZornSequence) :=
  colimit.ι ZornSequence j (zornCuntzGenerator j)

/--
A finite square-zero seed remains square-zero after insertion into the
categorical `ModuleCat` colimit under the witnessed descended multiplication.
-/
theorem continuumCuntz_sq_zero (j : J)
    (h : M.stageMul j (zornCuntzGenerator j) (zornCuntzGenerator j) = 0) :
    M.colimitMul
        (continuumCuntzGenerator R ZornSequence zornCuntzGenerator j)
        (continuumCuntzGenerator R ZornSequence zornCuntzGenerator j) = 0 := by
  exact CompatibleBilinearMultiplication.colimit_square_zero_of_stage
    (R := R) (ZornSequence := ZornSequence) M h

end InfoGeometry.Categorical.ZornBraidColimit
