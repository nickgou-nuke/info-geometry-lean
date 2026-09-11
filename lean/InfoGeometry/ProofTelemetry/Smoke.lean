import InfoGeometry.ProofTelemetry.Kernel
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
Small executable smoke checks for the Lean-native proof telemetry kernel.
-/

open InfoGeometry.ProofTelemetry

def demoTableauTrace : PaperproofTrace where
  id := "Demo.tableau"
  theoremName := "Demo.tableau"
  sourceFile := "InfoGeometry.ProofTelemetry.Smoke"
  steps := #[
    {
      index := 0
      tactic := "by_contra h"
      goalsBefore := #[{ id := "goal-before-0", text := "⊢ P" }]
      goalsAfter := #[{ id := "goal-after-0", text := "⊢ False" }]
      hypothesesBefore := #[]
      hypothesesAfter := #[{ id := "hyp-after-0", name := "h", type := "¬ P" }]
      references := #[]
    },
    {
      index := 1
      tactic := "contradiction"
      goalsBefore := #[{ id := "goal-before-1", text := "⊢ False" }]
      goalsAfter := #[]
      hypothesesBefore := #[{ id := "hyp-before-1", name := "h", type := "False" }]
      hypothesesAfter := #[]
      references := #[]
    }
  ]

def demoForest : ProofForest :=
  proofForest demoTableauTrace

#eval (tableauProfile demoTableauTrace).tableauLike
#eval (tableauProfile demoTableauTrace).falseGoalSteps
#eval tacticEffects demoTableauTrace.steps[0]!
#eval checkProofForest demoForest
