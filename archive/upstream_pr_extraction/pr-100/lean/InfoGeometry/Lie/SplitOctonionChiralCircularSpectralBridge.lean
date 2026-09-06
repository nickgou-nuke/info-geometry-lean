import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

/-!
# Chiral labels on the genuine circular Peirce basis

This owner is limited to the carrier-aligned basis readout. All definitions
use the canonical carrier owned by SplitOctonionEllCircularPeirceBasis.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionChiralCircularSpectralBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel

abbrev CZ := SplitOctonionEllCircularPeirceBasis.CanonicalZorn

def generatorIndex : ChiralGenerator → Fin 8
  | .pPlus => 0
  | .sPlus 0 => 1
  | .sPlus 1 => 2
  | .sPlus 2 => 3
  | .pMinus => 4
  | .sMinus 0 => 5
  | .sMinus 1 => 6
  | .sMinus 2 => 7

def generatorState (g : ChiralGenerator) : CZ :=
  circularPeirceBasis (generatorIndex g)

@[simp] theorem generatorState_pPlus : generatorState .pPlus = uPlus := by
  simp [generatorState, generatorIndex, circularPeirceBasis_apply, frame]

@[simp] theorem generatorState_pMinus : generatorState .pMinus = uMinus := by
  simp [generatorState, generatorIndex, circularPeirceBasis_apply, frame]

@[simp] theorem generatorState_sPlus (i : Fin 3) :
    generatorState (.sPlus i) = rootPlus i := by
  fin_cases i <;>
    simp [generatorState, generatorIndex, circularPeirceBasis_apply, frame]

@[simp] theorem generatorState_sMinus (i : Fin 3) :
    generatorState (.sMinus i) = rootMinus i := by
  fin_cases i <;>
    simp [generatorState, generatorIndex, circularPeirceBasis_apply, frame]

theorem generatorState_eq_circularPeirceBasis (g : ChiralGenerator) :
    generatorState g = circularPeirceBasis (generatorIndex g) := rfl

end InfoGeometry.Lie.SplitOctonionChiralCircularSpectralBridge
