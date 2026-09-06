import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import InfoGeometry.Topology.DelaunayFlipMatrix
import InfoGeometry.Topology.RohozhkinPentagonMatrix
import InfoGeometry.Topology.DelaunayPureBraidInvariant
import InfoGeometry.Topology.PureBraidGroup

/-!
# Matrix-unit embedding boundary for the Delaunay/Pure-braid owner

The genuine Delaunay owner supplies the flip-word matrix and its invariance
under the finite move relation.  The remaining presented-group step is
therefore exposed here through the native `PureBraid.lift` interface: a
concrete generator map and its relator proof are explicit inputs, not an
identity-valued property.
-/

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

/-
The historical names are retained for source compatibility, but no longer
manufacture an identity assignment.  They now expose the actual descent data
required by the presented-group owner.
-/
noncomputable def trivialPureBraidGeneratorAssignment (moving : ℕ)
    (gen : PureBraid.PureBraidGenerator (rohozhkinTotalPoints moving) →
      MatrixUnits (rohozhkinDim moving)) := gen

theorem trivial_pure_braid_generator_assignment_satisfies_relators
    (moving : ℕ)
    (gen : PureBraid.PureBraidGenerator (rohozhkinTotalPoints moving) →
      MatrixUnits (rohozhkinDim moving))
    (hrel : PureBraid.respectsPureBraidRelations gen) :
    PureBraid.respectsPureBraidRelations
      (trivialPureBraidGeneratorAssignment moving gen) := hrel

noncomputable def trivial_pure_braid_representation (moving : ℕ)
    (gen : PureBraid.PureBraidGenerator (rohozhkinTotalPoints moving) →
      MatrixUnits (rohozhkinDim moving))
    (hrel : PureBraid.respectsPureBraidRelations gen) :
    PureBraidRepresentationBoundary moving :=
  PureBraid.lift gen hrel

end GeneratorAssignment

end InfoGeometry.Topology.Delaunay
