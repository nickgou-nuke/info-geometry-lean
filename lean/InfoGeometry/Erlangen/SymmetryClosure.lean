/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Order.Closure

/-!
# Symmetry closure for an arbitrary group action

For an actual action of `G` on `X`, the subgroup closure sends `H` to the
subgroup fixing every `H`-fixed point. It is the closure operator induced by
Mathlib's fixing-subgroup/fixed-point Galois connection. No algebraic structure
on `X`, faithfulness, transitivity, topology, or analytic flow hypothesis is
needed.

The closure has the same fixed points as the original subgroup. Stabilizers
of points, and more generally pointwise fixing subgroups, are closed. This is
not a claim that the closure is the identity on every subgroup or that every
singleton subset of `X` is closed under the opposite fixed-point construction.

The final lemmas express joint stabilization and restriction to a subgroup
using native product actions, subgroup intersections, and subgroup preimages.
-/

namespace InfoGeometry.Erlangen.SymmetryClosure

variable {G X : Type*} [Group G] [MulAction G X]

/-- The subgroup/fixed-point correspondence for an arbitrary `G`-set. -/
theorem subgroup_le_fixingSubgroup_iff {H : Subgroup G} {S : Set X} :
    H ≤ _root_.fixingSubgroup G S ↔ S ⊆ MulAction.fixedPoints H X :=
  _root_.fixingSubgroup_fixedPoints_gc G X S H

/-- A point is fixed by `H` exactly when `H` lies in its stabilizer. -/
theorem mem_fixedPoints_iff_le_stabilizer (H : Subgroup G) (x : X) :
    x ∈ MulAction.fixedPoints H X ↔ H ≤ MulAction.stabilizer G x := by
  constructor
  · intro hx g hg
    exact hx ⟨g, hg⟩
  · intro hx g
    exact hx g.property

/-- The actual order-theoretic closure obtained by fixing all invariant points. -/
def subgroupClosure (G X : Type*) [Group G] [MulAction G X] :
    ClosureOperator (Subgroup G) :=
  (_root_.fixingSubgroup_fixedPoints_gc G X).dual.closureOperator

@[simp] theorem subgroupClosure_apply (H : Subgroup G) :
    subgroupClosure G X H =
      _root_.fixingSubgroup G (MulAction.fixedPoints H X) := rfl

/-- Membership states exactly which fixed points a symmetry must preserve. -/
theorem mem_subgroupClosure_iff (H : Subgroup G) (g : G) :
    g ∈ subgroupClosure G X H ↔
      ∀ x ∈ MulAction.fixedPoints H X, g • x = x :=
  _root_.mem_fixingSubgroup_iff G

/-- Every original symmetry belongs to the closure. -/
theorem le_subgroupClosure (H : Subgroup G) : H ≤ subgroupClosure G X H :=
  (subgroupClosure G X).le_closure H

/-- Enlarging the original symmetry subgroup enlarges its closure. -/
theorem subgroupClosure_monotone : Monotone (subgroupClosure G X) :=
  (subgroupClosure G X).monotone

/-- Taking the same symmetry closure twice adds nothing further. -/
@[simp] theorem subgroupClosure_idempotent (H : Subgroup G) :
    subgroupClosure G X (subgroupClosure G X H) = subgroupClosure G X H :=
  (subgroupClosure G X).idempotent H

/-- Closure preserves precisely the set of invariant points. -/
@[simp] theorem fixedPoints_subgroupClosure (H : Subgroup G) :
    MulAction.fixedPoints (subgroupClosure G X H) X =
      MulAction.fixedPoints H X :=
  (_root_.fixingSubgroup_fixedPoints_gc G X).u_l_u_eq_u H

/-- Every pointwise fixing subgroup is closed. -/
@[simp] theorem subgroupClosure_fixingSubgroup (S : Set X) :
    subgroupClosure G X (_root_.fixingSubgroup G S) =
      _root_.fixingSubgroup G S :=
  (_root_.fixingSubgroup_fixedPoints_gc G X).dual.u_l_u_eq_u S

/-- Pointwise stabilization of a singleton is the native point stabilizer. -/
@[simp] theorem fixingSubgroup_singleton (x : X) :
    _root_.fixingSubgroup G ({x} : Set X) = MulAction.stabilizer G x := by
  ext g
  simp [_root_.mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff]

/-- In particular, every point stabilizer is closed. -/
@[simp] theorem subgroupClosure_stabilizer (x : X) :
    subgroupClosure G X (MulAction.stabilizer G x) = MulAction.stabilizer G x := by
  rw [← fixingSubgroup_singleton x, subgroupClosure_fixingSubgroup]

/-- Passing to closure preserves every constraint of fixing a displayed point. -/
theorem subgroupClosure_le_stabilizer_iff (H : Subgroup G) (x : X) :
    subgroupClosure G X H ≤ MulAction.stabilizer G x ↔
      H ≤ MulAction.stabilizer G x := by
  constructor
  · intro h
    exact (le_subgroupClosure (X := X) H).trans h
  · intro h
    simpa only [subgroupClosure_stabilizer] using
      (subgroupClosure G X).monotone h

/-- Restricting the acting group takes the preimage of the ambient stabilizer. -/
theorem stabilizer_restrict_eq_comap (H : Subgroup G) (x : X) :
    MulAction.stabilizer H x = (MulAction.stabilizer G x).comap H.subtype := by
  ext g
  rfl

section JointStabilizer

variable {Y : Type*} [MulAction G Y]

/-- Stabilizing a pair means satisfying both native stabilizer conditions. -/
theorem stabilizer_prod_eq_inf (x : X) (y : Y) :
    MulAction.stabilizer G (x, y) =
      MulAction.stabilizer G x ⊓ MulAction.stabilizer G y := by
  ext g
  change (g • x, g • y) = (x, y) ↔ g • x = x ∧ g • y = y
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hx, hy⟩
    exact Prod.ext hx hy

/-- After fixing the first object, joint stabilization is the stabilizer of
the second object under the restricted action. -/
theorem joint_stabilizer_comap_left (x : X) (y : Y) :
    (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y).comap
        (MulAction.stabilizer G x).subtype =
      MulAction.stabilizer (MulAction.stabilizer G x) y := by
  ext g
  change ((g : G) • x = x ∧ (g : G) • y = y) ↔ (g : G) • y = y
  exact ⟨And.right, fun hy => ⟨g.property, hy⟩⟩

/-- Closure for the product action preserves a joint stabilization constraint. -/
theorem subgroupClosure_le_joint_stabilizer_iff (H : Subgroup G) (x : X) (y : Y) :
    subgroupClosure G (X × Y) H ≤
        MulAction.stabilizer G x ⊓ MulAction.stabilizer G y ↔
      H ≤ MulAction.stabilizer G x ⊓ MulAction.stabilizer G y := by
  rw [← stabilizer_prod_eq_inf x y]
  exact subgroupClosure_le_stabilizer_iff H (x, y)

end JointStabilizer

end InfoGeometry.Erlangen.SymmetryClosure
