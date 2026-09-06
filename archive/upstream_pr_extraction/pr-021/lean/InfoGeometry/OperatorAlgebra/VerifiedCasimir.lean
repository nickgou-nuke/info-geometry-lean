/-
InfoGeometry/OperatorAlgebra/VerifiedCasimir.lean

The Individuation of the Casimir Invariant.
Eliminating the Dark Energy Shadow.

Following the Erlangen Program for Operator Algebras, geometry is defined
as the algebraic invariants of the symmetry action.  The Casimir element
is the fundamental constructive witness for this geometry.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.SymmetryInvariants

noncomputable section

namespace IndividuatedCasimir

open InfoGeometry.OperatorAlgebra

/-! ## 1. The Algebraic Socket (Albedo) -/

/--
A constructively verified Operator Casimir.
This replaces the vacuous "Dark Energy" or "Topological Charge" prose.

A Casimir must be:
1. Invariant under the symmetry action (Erlanger Invariant).
2. Central in the operator algebra (Superselection Rule).
-/
structure VerifiedCasimir
    {Op : Type*} [Ring Op]
    {G : Type*} [Group G]
    (α : SymmetryAction G Op) where
  /-- The Casimir element in the algebra. -/
  C : Op

  /-- The Casimir is fixed under the symmetry group action. -/
  is_invariant : IsInvariant α C

  /-- The Casimir commutes with all observables (centrality). -/
  is_central : ∀ x : Op, C * x = x * C

namespace VerifiedCasimir

variable {Op : Type*} [Ring Op] {G : Type*} [Group G] {α : SymmetryAction G Op}

/-- A Casimir belongs to the center of the operator algebra. -/
theorem mem_center (V : VerifiedCasimir α) :
    V.C ∈ Subring.center Op := by
  rw [Subring.mem_center_iff]
  intro x
  rw [V.is_central x]

/-- A Casimir belongs to the invariant subring. -/
theorem mem_invariantSubring (V : VerifiedCasimir α) :
    V.C ∈ invariantSubring α :=
  V.is_invariant

end VerifiedCasimir

/-! ## 2. Rubedo Phase: Construction of the Cl(4,4) Casimir -/

/- 
Note: The following is a template for the constructive synthesis. 
In the full repository, we would link this to the DiracSouriau operator
on the Clifford algebra Cl(4,4).
-/

end IndividuatedCasimir

