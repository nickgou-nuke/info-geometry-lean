import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Physics.G2BdGPairingSoldering

open ContinuousLinearMap

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H
local notation "NambuH" => H × H
local notation "EndNambu" => NambuH →L[ℂ] NambuH

structure G2DerivationPairing (E : Type*) where
  normalA : E
  pairingDelta : E

noncomputable def g2_bdg_operator (D : G2DerivationPairing EndH) : EndNambu :=
  (D.normalA.coprod D.pairingDelta).prod
    ((ContinuousLinearMap.adjoint D.pairingDelta).coprod (-ContinuousLinearMap.adjoint D.normalA))

def block12 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.fst ℂ H H).comp (T.comp (ContinuousLinearMap.inr ℂ H H))

@[simp]
theorem block12_g2_bdg_operator (D : G2DerivationPairing EndH) :
    block12 (g2_bdg_operator D) = D.pairingDelta := by
  apply ContinuousLinearMap.ext
  intro v
  simp [block12, g2_bdg_operator, ContinuousLinearMap.comp_apply]

theorem g2_pairing_soldering_theorem (D : G2DerivationPairing EndH) :
    block12 (g2_bdg_operator D) = D.pairingDelta :=
  block12_g2_bdg_operator D

end InfoGeometry.Physics.G2BdGPairingSoldering

end noncomputable section
