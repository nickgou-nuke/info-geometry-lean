/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from AxiomMath/CFSG, Apache-2.0. This is the catalog predicate only;
it does not import or prove the external classification theorem.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ClassicalCatalog
public import InfoGeometry.Exceptional.CFSGPort.ExceptionalCatalog
public import InfoGeometry.Exceptional.CFSGPort.SporadicGroups

public section

namespace InfoGeometry.Exceptional.CFSGPort

/--
The finite-group model catalog appearing in CFSG: cyclic prime-order,
alternating, classical Lie-type, exceptional Lie-type, and sporadic models.
This predicate says that a group has one of these models; it does not assert
that the group is simple or that every finite simple group satisfies it.
-/
@[expose] def FiniteGroupModelCatalog (G : Type) [Group G] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    Classical.Catalog G ∨ Chevalley.ExceptionalLieCatalog G ∨
    Sporadic.SporadicRep G

end InfoGeometry.Exceptional.CFSGPort

end
