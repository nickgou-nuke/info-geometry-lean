import InfoGeometry.ProofTelemetry.Kernel

/-!
Small executable smoke checks for the Lean-native proof telemetry kernel.
-/

open InfoGeometry.ProofTelemetry

def demoTableauTrace : PaperproofTrace where
  id := "Demo.tableau"
  theoremName := "Demo.tableau"
  steps := #[
    {
      index := 0
      tactic := "by_contra h"
      goalsBefore := #[{ text := "⊢ P" }]
      goalsAfter := #[{ text := "⊢ False" }]
      hypothesesAfter := #[{ name := "h", type := "¬ P" }]
    },
    {
      index := 1
      tactic := "contradiction"
      goalsBefore := #[{ text := "⊢ False" }]
      goalsAfter := #[]
      hypothesesBefore := #[{ name := "h", type := "False" }]
    }
  ]

def demoForest : ProofForest :=
  proofForest demoTableauTrace

#eval (tableauProfile demoTableauTrace).tableauLike
#eval (tableauProfile demoTableauTrace).falseGoalSteps
#eval tacticEffects demoTableauTrace.steps[0]!
#eval checkProofForest demoForest
