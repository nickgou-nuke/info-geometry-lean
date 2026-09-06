import InfoGeometry.Canonical.HexIndexSplitOctonionBridge
import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms

namespace InfoGeometry.Canonical

open HexagonalSixRootTiling
open SplitOctonionColour

noncomputable section

def colourSuccessor : SplitOctonionColour → SplitOctonionColour
  | .red => .green
  | .green => .blue
  | .blue => .red

def fin3Successor : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

theorem colourFin3Equiv_fin3Successor (c : Fin 3) :
    colourFin3Equiv (fin3Successor c) =
      colourSuccessor (colourFin3Equiv c) := by
  fin_cases c <;> rfl

theorem trialityColorCycle_rationalBasis (b : IntegralSplitBasis) :
    trialityColorCycle (rationalBasis b) =
      rationalBasis (colorCycleBasis b) := by
  ext d
  cases b <;> cases d <;>
    simp [trialityColorCycle, colorCycleBasisEquiv, colorCycleBasis,
      colorCycleBasisInv, rationalBasis, Pi.single_apply]

theorem trialityColorCycle_colourLUnit (c : SplitOctonionColour) :
    trialityColorCycle (colourLUnit c) =
      colourLUnit (colourSuccessor c) := by
  cases c <;>
    simp [colourLUnit, colourSuccessor, colorCycleBasis,
      trialityColorCycle_rationalBasis]

theorem trialityColorCycle_modularSigmaPlus (c : SplitOctonionColour) :
    trialityColorCycle (modularSigmaPlus c) =
      modularSigmaPlus (colourSuccessor c) := by
  cases c <;>
    simp [modularSigmaPlus, modularJ_eq_colourLUnit, phaseAxis,
      colourUnit, colourSuccessor, trialityColorCycle_rationalBasis,
      trialityColorCycle_colourLUnit, colorCycleBasis]

theorem trialityColorCycle_modularSigmaMinus (c : SplitOctonionColour) :
    trialityColorCycle (modularSigmaMinus c) =
      modularSigmaMinus (colourSuccessor c) := by
  cases c <;>
    simp [modularSigmaMinus, modularJ_eq_colourLUnit, phaseAxis,
      colourUnit, colourSuccessor, trialityColorCycle_rationalBasis,
      trialityColorCycle_colourLUnit, colorCycleBasis]

theorem trialityColorCycle_sixSectorBasisFin3
    (s : Fin 2) (c : Fin 3) :
    trialityColorCycle (sixSectorBasisFin3 s c) =
      sixSectorBasisFin3 s (fin3Successor c) := by
  fin_cases s <;> fin_cases c <;>
    simp [sixSectorBasisFin3, sixSectorBasis, colourFin3Equiv,
      fin3Successor, colourSuccessor, trialityColorCycle_modularSigmaPlus,
      trialityColorCycle_modularSigmaMinus]

end
end InfoGeometry.Canonical
