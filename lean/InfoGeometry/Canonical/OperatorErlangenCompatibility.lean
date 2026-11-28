/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorErlangenGaloisConnection
import InfoGeometry.Erlangen.SymmetryClosure

/-!
# Compatibility of operator invariants with general symmetry closure

The existing semiring-action definitions agree with Mathlib's general
fixing-subgroup and fixed-point constructions. Consequently the new subgroup
closure is exactly the old operator double-fixing operation, and it preserves
the old fixed-point subsemiring. The algebraic carrier and its noncommutative
multiplication are unchanged.

These equalities leave the declarations and binders of the operator owners
intact. They do not assert that every subgroup is closed or promote the
Galois connection to an anti-equivalence on all subgroups and observables.
-/

namespace InfoGeometry.Canonical.OperatorErlangenCompatibility

variable {G A : Type*} [Group G] [Semiring A] [MulSemiringAction G A]

/-- The old operator fixer is the native pointwise fixing subgroup. -/
theorem operator_fixingSubgroup_eq_native (S : Set A) :
    OperatorErlangenFixedPoints.fixingSubgroup (G := G) S =
      _root_.fixingSubgroup G S := by
  ext g
  exact (OperatorErlangenFixedPoints.mem_fixingSubgroup_iff S g).trans
    (_root_.mem_fixingSubgroup_iff G).symm

/-- The old fixed-observable set is definitionally the native fixed-point set. -/
theorem operator_fixedPointSet_eq_native (H : Subgroup G) :
    OperatorErlangenFixedPoints.fixedPointSet (A := A) H =
      MulAction.fixedPoints H A := rfl

/-- General symmetry closure reads back as the existing operator double fixer. -/
theorem subgroupClosure_eq_operator_doubleFix (H : Subgroup G) :
    Erlangen.SymmetryClosure.subgroupClosure G A H =
      OperatorErlangenFixedPoints.fixingSubgroup (G := G)
        (OperatorErlangenFixedPoints.fixedPointSet (A := A) H) := by
  simpa only [operator_fixingSubgroup_eq_native, operator_fixedPointSet_eq_native] using
    Erlangen.SymmetryClosure.subgroupClosure_apply (X := A) H

/-- Passing to the general symmetry closure preserves the entire existing
fixed-point subsemiring, including its multiplication. -/
theorem operator_fixedPointSubsemiring_subgroupClosure (H : Subgroup G) :
    OperatorErlangenFixedPoints.fixedPointSubsemiring (A := A)
        (Erlangen.SymmetryClosure.subgroupClosure G A H) =
      OperatorErlangenFixedPoints.fixedPointSubsemiring (A := A) H := by
  apply SetLike.coe_injective
  change OperatorErlangenFixedPoints.fixedPointSet
      (Erlangen.SymmetryClosure.subgroupClosure G A H) =
    OperatorErlangenFixedPoints.fixedPointSet H
  exact (operator_fixedPointSet_eq_native _).trans
    ((Erlangen.SymmetryClosure.fixedPoints_subgroupClosure (X := A) H).trans
      (operator_fixedPointSet_eq_native H).symm)

end InfoGeometry.Canonical.OperatorErlangenCompatibility
