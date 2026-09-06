import InfoGeometry.Topology.DelaunayPureBraidInvariant
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

/-- The trivial matrix-unit assignment sends every pure-braid generator to `1`. -/
def trivialPureBraidGenerator (moving : ℕ) :
    PureBraidGenerator (rohozhkinTotalPoints moving) → RohozhkinMatrixUnits moving :=
  fun _ => 1

/-- The trivial assignment satisfies all pure-braid relators. -/
theorem trivialPureBraidGenerator_respects (moving : ℕ) :
    respectsPureBraidRelations (trivialPureBraidGenerator moving) := by
  intro r hr
  rcases hr with
    (⟨i, j, k, l, hij, hkl, hshape, rfl⟩ | ⟨i, j, k, hij, hjk, rfl⟩ |
      ⟨i, j, k, hij, hjk, rfl⟩ | ⟨i, j, k, l, hij, hjk, hkl, rfl⟩)
  · simp [trivialPureBraidGenerator, farCommRelator, relatorEq, b]
  · simp [trivialPureBraidGenerator, tripleRelatorLeft, relatorEq, b]
  · simp [trivialPureBraidGenerator, tripleRelatorRight, relatorEq, b]
  · simp [trivialPureBraidGenerator, quadrupleRelator, relatorEq, b]

/-- The trivial pure-braid representation descends to a group homomorphism. -/
noncomputable def trivialPureBraidRepresentation (moving : ℕ) :
    RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving :=
  pureBraidMatrixRepresentationOfRelators moving (trivialPureBraidGenerator moving)
    (trivialPureBraidGenerator_respects moving)

/-- Generator readout for the trivial descended representation. -/
@[simp]
theorem trivialPureBraidRepresentation_of (moving : ℕ)
    (g : PureBraidGenerator (rohozhkinTotalPoints moving)) :
    trivialPureBraidRepresentation moving (of g) = 1 := by
  simp [trivialPureBraidRepresentation, trivialPureBraidGenerator]

/-- Concrete descent packet for the trivial pure-braid representation. -/
theorem trivial_pureBraid_descent_packet (moving : ℕ) :
    respectsPureBraidRelations (trivialPureBraidGenerator moving) ∧
    ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
      ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving), ρ (of g) = 1 := by
  exact ⟨trivialPureBraidGenerator_respects moving,
    ⟨trivialPureBraidRepresentation moving,
      trivialPureBraidRepresentation_of moving⟩⟩

end InfoGeometry.Topology.RohozhkinBoundary
