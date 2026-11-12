/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CharacterRelationQuotient
import InfoGeometry.Algebra.CyclicQuotient
import Mathlib.Algebra.FreeAlgebra
import Mathlib.GroupTheory.Perm.Finite

/-!
# Permutation symmetry of free noncommutative operators

Renaming the generators of a native `FreeAlgebra` gives a genuine group
representation. Its algebra maps preserve the existing commutator relation
space, so the character-sector quotient equivalence applies to this actual
noncommutative carrier. Renaming does not reorder factors in a word.

The cyclic quotient imposes universal linear cyclicity only. It does not
encode all matrix trace identities, equations of motion, or Fierz relations.
-/

noncomputable section

namespace InfoGeometry.Algebra.FreeOperatorSymmetry

open FiniteGroupCharacterProjection CharacterRelationQuotient CyclicQuotient

variable (k : Type*) {ι : Type*} [CommRing k]

/-- Rename generators without changing the order of multiplication. -/
def rename (g : Equiv.Perm ι) : FreeAlgebra k ι →ₐ[k] FreeAlgebra k ι :=
  FreeAlgebra.lift k (fun i => FreeAlgebra.ι k (g i))

@[simp] theorem rename_ι (g : Equiv.Perm ι) (i : ι) :
    rename k g (FreeAlgebra.ι k i) = FreeAlgebra.ι k (g i) := by
  simp [rename]

theorem rename_one : rename k (1 : Equiv.Perm ι) = AlgHom.id k (FreeAlgebra k ι) := by
  apply FreeAlgebra.hom_ext
  funext i
  simp

theorem rename_mul (g h : Equiv.Perm ι) :
    rename k (g * h) = (rename k g).comp (rename k h) := by
  apply FreeAlgebra.hom_ext
  funext i
  simp

/-- The generator-permutation action on the entire free associative algebra. -/
def representation : Representation k (Equiv.Perm ι) (FreeAlgebra k ι) where
  toFun g := (rename k g).toLinearMap
  map_one' := by
    rw [rename_one]
    rfl
  map_mul' g h := by
    rw [rename_mul]
    rfl

@[simp] theorem representation_apply (g : Equiv.Perm ι) (a : FreeAlgebra k ι) :
    representation k g a = rename k g a := rfl

/-- Stability is derived from the algebra maps, not postulated for arbitrary linear maps. -/
theorem commutator_stable (g : Equiv.Perm ι) :
    commutatorSpan k (FreeAlgebra k ι) ≤
      (commutatorSpan k (FreeAlgebra k ι)).comap (representation k g) :=
  commutatorSpan_le_comap_algHom (rename k g)

section Finite

variable [Fintype ι] [DecidableEq ι]
  [Invertible (Fintype.card (Equiv.Perm ι) : k)]

/-- The canonical sector quotient equivalence for permutation-symmetric free words modulo
the explicit cyclic relation space. The ambient free algebra is not assumed finite dimensional. -/
def cyclicSectorEquiv (χ : Equiv.Perm ι →* kˣ) :
    (sector (representation k) χ ⧸
      (commutatorSpan k (FreeAlgebra k ι)).comap (sector (representation k) χ).subtype) ≃ₗ[k]
      sector ((representation k).quotient (commutatorSpan k (FreeAlgebra k ι))
        (commutator_stable k)) χ :=
  sectorQuotientEquiv (representation k) χ _ (commutator_stable k)

@[simp] theorem cyclicSectorEquiv_mk (χ : Equiv.Perm ι →* kˣ)
    (a : sector (representation k) χ) :
    (cyclicSectorEquiv k χ (Submodule.Quotient.mk a) : CyclicModule k (FreeAlgebra k ι)) =
      cyclicClass k (FreeAlgebra k ι) (a : FreeAlgebra k ι) := rfl

end Finite

end InfoGeometry.Algebra.FreeOperatorSymmetry
