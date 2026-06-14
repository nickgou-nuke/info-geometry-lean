import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import InfoGeometry.Topology.DelaunayFlipMatrix
import InfoGeometry.Topology.RohozhkinPentagonMatrix
import InfoGeometry.Topology.DelaunayPureBraidInvariant
import InfoGeometry.Topology.PureBraidGroup

/-!
# Matrix-unit embedding sockets for the Delaunay/Pure-braid boundary

This file currently provides only the trivial presented-group descent obtained
by sending every pure-braid generator to the identity matrix unit.  It is useful
as an API/socket check for `PureBraid.lift`, but it is **not** Rohozhkin's
nontrivial Delaunay monodromy representation.

The real Rohozhkin descent remains the separate obligation: construct the
nontrivial generator assignment from Delaunay flip matrices and prove all
`PureBraid.pureBraidRelations` are killed.
-/

set_option linter.unusedSimpArgs false

namespace InfoGeometry.Topology.Delaunay

open Matrix

noncomputable def embedBlock₂ (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) : Matrix (Fin d) (Fin d) ℚ :=
  λ i j =>
    if i = a then
      if j = a then block 0 0
      else if j = b then block 0 1
      else 0
    else if i = b then
      if j = a then block 1 0
      else if j = b then block 1 1
      else 0
    else if i = j then 1 else 0

section GeneratorAssignment

open PureBraid

variable (moving : ℕ)

local notation "d" => rohozhkinDim moving
local notation "m" => rohozhkinTotalPoints moving

/-- Trivial generator assignment used only to test the `PresentedGroup` descent API. -/
noncomputable def trivialPureBraidGeneratorAssignment (moving : ℕ) :
    PureBraid.PureBraidGenerator (rohozhkinTotalPoints moving) → MatrixUnits (rohozhkinDim moving) :=
  λ _ => ⟨1, 1, by simp, by simp⟩

/-- The trivial assignment kills all relators.  This is not the Rohozhkin matrix assignment. -/
theorem trivial_pure_braid_generator_assignment_satisfies_relators (moving : ℕ) :
    PureBraid.respectsPureBraidRelations (trivialPureBraidGeneratorAssignment moving) := by
  intro r hr
  have h_const : trivialPureBraidGeneratorAssignment moving = λ _ => (1 : MatrixUnits (rohozhkinDim moving)) := by
    ext g; simp [trivialPureBraidGeneratorAssignment]
  rw [h_const]
  have h_triv : FreeGroup.lift (λ _ : PureBraid.PureBraidGenerator (rohozhkinTotalPoints moving) =>
    (1 : MatrixUnits (rohozhkinDim moving))) = (1 : _ →* _) := by
    ext x; simp
  rw [h_triv]
  simp

/-- Trivial pure-braid representation into matrix units.

This is a compatibility/socket construction only.  It should not be cited as
Rohozhkin's nontrivial Delaunay representation. -/
noncomputable def trivial_pure_braid_representation (moving : ℕ) :
    PureBraidRepresentationBoundary moving :=
  PureBraid.lift (trivialPureBraidGeneratorAssignment moving)
    (trivial_pure_braid_generator_assignment_satisfies_relators moving)

end GeneratorAssignment

end InfoGeometry.Topology.Delaunay
