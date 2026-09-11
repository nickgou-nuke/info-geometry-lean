import InfoGeometry.Topology.DelaunayPureBraidInvariant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.PureBraidGroup

/-!
# Pure-braid matrix representations by presented-group descent

This module contains the only theorem-safe general statement currently available
for a pure-braid matrix representation in the Rohozhkin/Delaunay layer:

if a generator assignment into rational matrix units sends every relator in the
mathlib `PresentedGroup` presentation to `1`, then it descends to a group
homomorphism from the presented pure braid group.

It does not construct Rohozhkin's nontrivial generator assignment.
-/

namespace InfoGeometry.Topology.RohozhkinBoundary

open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid

/-- The matrix-unit target for the Rohozhkin dimension associated to `moving`. -/
abbrev RohozhkinMatrixUnits (moving : ℕ) :=
  MatrixUnits (rohozhkinDim moving)

/-- The source presented pure braid group on `moving + 3` strands. -/
abbrev RohozhkinPureBraidGroup (moving : ℕ) :=
  RohozhkinSourcePB moving

/--
Genuine presented-group descent theorem for matrix-unit representations.

To obtain an actual Rohozhkin representation, instantiate `gen` with the real
Delaunay/Rohozhkin generator matrices and prove `hrel`.  This theorem is only
the mathlib descent step, via `PresentedGroup.toGroup`.
-/
noncomputable def pureBraidMatrixRepresentationOfRelators (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) → RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen) :
    RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving :=
  lift gen hrel

@[simp]
theorem pureBraidMatrixRepresentationOfRelators_of (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) → RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen)
    (g : PureBraidGenerator (rohozhkinTotalPoints moving)) :
    pureBraidMatrixRepresentationOfRelators moving gen hrel (of g) = gen g := by
  simp [pureBraidMatrixRepresentationOfRelators]

/--
Existence form of the same descent theorem, avoiding any invented packet or
boundary structure.
-/
theorem exists_pureBraidMatrixRepresentation_of_relators (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) → RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen) :
    ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
      ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving), ρ (of g) = gen g := by
  exact ⟨pureBraidMatrixRepresentationOfRelators moving gen hrel,
    pureBraidMatrixRepresentationOfRelators_of moving gen hrel⟩

/-
The historical identity assignment was only a vacuous compatibility witness.
Retain the names as a migration surface, but route them directly through the
generic native descent theorem with an explicit generator assignment and
relator proof.
-/
def trivialPureBraidGenerator (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) →
      RohozhkinMatrixUnits moving) := gen

theorem trivialPureBraidGenerator_respects (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) →
      RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen) :
    respectsPureBraidRelations (trivialPureBraidGenerator moving gen) := hrel

noncomputable def trivialPureBraidRepresentation (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) →
      RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen) :
    RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving :=
  pureBraidMatrixRepresentationOfRelators moving gen hrel

@[simp]
theorem trivialPureBraidRepresentation_of (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) →
      RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen)
    (g : PureBraidGenerator (rohozhkinTotalPoints moving)) :
    trivialPureBraidRepresentation moving gen hrel (of g) = gen g := by
  exact pureBraidMatrixRepresentationOfRelators_of moving gen hrel g

theorem trivial_pureBraid_descent_packet (moving : ℕ)
    (gen : PureBraidGenerator (rohozhkinTotalPoints moving) →
      RohozhkinMatrixUnits moving)
    (hrel : respectsPureBraidRelations gen) :
    respectsPureBraidRelations (trivialPureBraidGenerator moving gen) ∧
    ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
      ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving), ρ (of g) = gen g := by
  exact ⟨hrel, ⟨trivialPureBraidRepresentation moving gen hrel,
    trivialPureBraidRepresentation_of moving gen hrel⟩⟩

end InfoGeometry.Topology.RohozhkinBoundary
