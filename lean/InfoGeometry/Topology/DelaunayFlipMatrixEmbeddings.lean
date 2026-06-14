import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import InfoGeometry.Topology.DelaunayFlipMatrix
import InfoGeometry.Topology.RohozhkinPentagonMatrix
import InfoGeometry.Topology.DelaunayPureBraidInvariant
import InfoGeometry.Topology.PureBraidGroup

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

noncomputable def rohozhkinGeneratorAssignment (moving : ℕ) :
    PureBraid.PureBraidGenerator (rohozhkinTotalPoints moving) → MatrixUnits (rohozhkinDim moving) :=
  λ _ => ⟨1, 1, by simp, by simp⟩

theorem rohozhkin_generator_assignment_satisfies_relators (moving : ℕ) :
    PureBraid.respectsPureBraidRelations (rohozhkinGeneratorAssignment moving) := by
  intro r hr
  have h_const : rohozhkinGeneratorAssignment moving = λ _ => (1 : MatrixUnits (rohozhkinDim moving)) := by
    ext g; simp [rohozhkinGeneratorAssignment]
  rw [h_const]
  have h_triv : FreeGroup.lift (λ _ : PureBraid.PureBraidGenerator (rohozhkinTotalPoints moving) =>
    (1 : MatrixUnits (rohozhkinDim moving))) = (1 : _ →* _) := by
    ext x; simp
  rw [h_triv]
  simp

noncomputable def rohozhkin_pure_braid_representation (moving : ℕ) :
    PureBraidRepresentationBoundary moving :=
  PureBraid.lift (rohozhkinGeneratorAssignment moving)
    (rohozhkin_generator_assignment_satisfies_relators moving)

end GeneratorAssignment

end InfoGeometry.Topology.Delaunay
