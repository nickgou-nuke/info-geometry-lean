import Mathlib
import InfoGeometry.Canonical.ModularCoproductFlux
import InfoGeometry.Canonical.CoproductToVirasoroCocycleBridge

/-!
# InfoGeometry.Bridge.VirasoroCrossFluxCocycleBridge

Closure debt interface: connects the finite cross-flux `N ⊗ N` to the
continuous Virasoro cocycle.

This is a pure interface marking the exact debt required to rigorously
identify the finite coproduct defect with the infinite Virasoro central charge.
It does not claim to prove the limit.
-/

namespace VirasoroProject.Extensions.VirasoroCrossFluxCocycleBridge

/--
Closure debt: an exact mathematical map connecting the finite-stage
`crossFlux N` readout to the value `(m^3 - m)/12` of the Witt-Virasoro cocycle.

This is a ledger entry for the future continuous limit theorem, not a proved
theorem in this bridge file.
-/
theorem crossFlux_yields_virasoroCocycle_debt
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : InfoGeometry.Canonical.CoproductToVirasoroCocycleBridge.NilpotentFluxReadout A)
    (m : Int) :
    InfoGeometry.Canonical.CoproductToVirasoroCocycleBridge.splitChannelRelativeEntropy
        (A := A) S m (-m) 2 =
      (S.ρ (InfoGeometry.Canonical.ModularCoproductFlux.crossFlux
        (R := ℝ) S.N) / 12) * (((m : ℝ) ^ 3) - (m : ℝ)) :=
  InfoGeometry.Canonical.CoproductToVirasoroCocycleBridge.splitChannelRelativeEntropy_two_step_resonant
    S m

end VirasoroProject.Extensions.VirasoroCrossFluxCocycleBridge
