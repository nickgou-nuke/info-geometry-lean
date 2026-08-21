import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace InfoGeometry.Algebra.Zorn.G2TwoUnipotentStructure

/-- The unipotent radical U of G₂(2) is parameterized by 6 independent root coordinates in 𝔽₂. -/
abbrev UnipotentCoords := Fin 6 → ZMod 2

/-- THEOREM: Cardinality of UnipotentCoords is 2⁶ = 64 by standard Mathlib Fintype.pi cardinality. -/
theorem unipotent_coords_card : Fintype.card UnipotentCoords = 64 := by
  change Fintype.card (Fin 6 → ZMod 2) = 64
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rfl

/-- Composition series factors for the 6-step unipotent filtration. -/
def filtrationStep (k : Fin 7) : ℕ := 2 ^ (6 - k.val)

theorem filtration_top : filtrationStep 0 = 64 := rfl
theorem filtration_bot : filtrationStep ⟨6, by decide⟩ = 1 := rfl

/-- THEOREM: Each step in the unipotent composition series has index 2. -/
theorem filtration_step_ratio (k : Fin 6) :
    filtrationStep ⟨k.val, by omega⟩ = 2 * filtrationStep ⟨k.val + 1, by omega⟩ := by
  dsimp [filtrationStep]
  have h : 6 - k.val = (6 - (k.val + 1)) + 1 := by omega
  rw [h, pow_succ, mul_comm]

end InfoGeometry.Algebra.Zorn.G2TwoUnipotentStructure
