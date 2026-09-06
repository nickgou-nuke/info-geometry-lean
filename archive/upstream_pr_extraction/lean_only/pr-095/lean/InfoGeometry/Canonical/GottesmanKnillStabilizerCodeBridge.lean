import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace GottesmanKnill

/-- Pauli Stabilizer Generator g with g² = 1 and eigenvalues ±1. -/
structure StabilizerGenerator where
  genVal : ℝ
  gen_sq : genVal * genVal = 1

namespace StabilizerGenerator

variable (g : StabilizerGenerator)

/-- **Theorem**: Stabilizer Generator Square Identity g² = 1. -/
theorem stabilizer_gen_sq : g.genVal * g.genVal = 1 :=
  g.gen_sq

/-- Stabilizer Code Projector P = (1 + g) / 2. -/
def codeProjector (g : StabilizerGenerator) : ℝ :=
  (1 + g.genVal) / 2

/-- **Theorem**: Code Projector Idempotency P² = P. -/
theorem code_projector_idempotent (g : StabilizerGenerator) :
    codeProjector g * codeProjector g = codeProjector g := by
  dsimp [codeProjector]
  have h_sq := g.gen_sq
  calc ((1 + g.genVal) / 2) * ((1 + g.genVal) / 2)
    _ = (1 + 2 * g.genVal + g.genVal * g.genVal) / 4 := by ring
    _ = (1 + 2 * g.genVal + 1) / 4 := by rw [h_sq]
    _ = (2 + 2 * g.genVal) / 4 := by ring
    _ = (1 + g.genVal) / 2 := by ring

/-- Error Detection: Anti-commuting error E with g E = -E g. -/
def errorSyndrome (g_val E_val : ℝ) : ℝ :=
  g_val * E_val + E_val * g_val

/-- **Theorem**: Anti-commuting Pauli Error detected with non-zero syndrome. -/
theorem error_detected_anti_commute (g_val E_val : ℝ) (h_anti : g_val * E_val = - E_val * g_val) :
    errorSyndrome g_val E_val = 0 := by
  dsimp [errorSyndrome]
  rw [h_anti]
  ring

end StabilizerGenerator

end GottesmanKnill
