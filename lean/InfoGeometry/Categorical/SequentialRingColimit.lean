/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# The existing sequential ring direct limit as a categorical colimit

This module supplies a native `RingCat` diagram and `IsColimit` witness for
`DirectLimitSuperClosureLemmas.DirectLimitSuperClosure`. All transition maps,
the carrier, the canonical ring homomorphisms and the universal lift are
reused from that owner. No new quotient or ring operations are introduced.
-/

noncomputable section

namespace InfoGeometry.Categorical.SequentialRingColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

variable {Stage : ℕ → Type u} [∀ k, Ring (Stage k)]
variable (bond : ∀ k, Stage k →+* Stage (k + 1))

/-- The preorder-category diagram of an existing one-step ring tower. -/
def diagram : ℕ ⥤ RingCat.{u} where
  obj k := RingCat.of (Stage k)
  map f := RingCat.ofHom (bondMap bond _ _ (leOfHom f))
  map_id k := by
    apply RingCat.hom_ext
    exact bondMap_refl bond k
  map_comp f g := by
    ext x
    exact bondMap_apply_trans bond _ _ _ (leOfHom f) (leOfHom g) x

/-- The successor arrow of the categorical diagram is the given bond. -/
@[simp]
theorem diagram_map_succ (k : ℕ) :
    (diagram bond).map (homOfLE (Nat.le_succ k)) = RingCat.ofHom (bond k) := by
  apply RingCat.hom_ext
  change bondMap bond k (k + 1) (Nat.le_succ k) = bond k
  rw [bondMap_succ bond k k le_rfl, bondMap_refl, RingHom.comp_id]

/-- The canonical cocone uses precisely the existing algebraic direct limit. -/
def cocone : Cocone (diagram bond) where
  pt := RingCat.of (DirectLimitSuperClosure bond)
  ι :=
    { app := fun k => RingCat.ofHom (directLimitOf bond k)
      naturality := by
        intro i j f
        ext x
        exact directLimitOf_bondMap bond i j (leOfHom f) x }

/-- Native categorical cocone naturality supplies the one-step compatibility
needed by the existing universal ring-homomorphism lift. -/
theorem cocone_compatible (s : Cocone (diagram bond)) :
    CompatibleCone (Limit := s.pt) bond (fun k => (s.ι.app k).hom) := by
  intro k x
  have h := s.w (homOfLE (Nat.le_succ k))
  rw [diagram_map_succ] at h
  exact ConcreteCategory.congr_hom h x

/-- Every categorical cocone descends through the existing algebraic lift. -/
def descend (s : Cocone (diagram bond)) : (cocone bond).pt ⟶ s.pt :=
  RingCat.ofHom
    (directLimitLift (Limit := s.pt) bond (fun k => (s.ι.app k).hom)
      (cocone_compatible bond s))

/-- The concrete direct-limit carrier satisfies the native categorical
universal property, including uniqueness. -/
def isColimit : IsColimit (cocone bond) where
  desc := descend bond
  fac s k := by
    ext x
    rfl
  uniq s m hm := by
    apply RingCat.hom_ext
    apply directLimitLift_unique (Limit := s.pt) bond (fun k => (s.ι.app k).hom)
      (cocone_compatible bond s) m.hom
    intro k
    exact congrArg RingCat.Hom.hom (hm k)

end InfoGeometry.Categorical.SequentialRingColimit
