import InfoGeometry.GrandUnification.AlgebraicSouriauTomita

/-!
# Modular transport, theorem-stack version

This module removes the former data-packet version of the grand modular
transport bridge.  It proves only the finite commuting Cartan transport surface
that is already owned by `InfoGeometry.Thermodynamics.FiniteConnesCocycle`.

What this module proves:

* the native operator-valued Connes cocycle satisfies its cocycle law on the
  doubled endomorphism algebra;
* the corrected Souriau--Tomita roadmap target is available as a theorem-stack
  conjunction.

What this module does not prove:

* full Tomita--Takesaki theory for von Neumann algebras;
* analytic Connes cocycle support/faithfulness/partial-isometry conditions;
* Gromov, Berry, Perelman, or spectral-normalization comparison theorems.
-/

noncomputable section

namespace InfoGeometry.GrandUnification

/-- Operatorial modular transport theorem from the native Connes owner. -/
theorem modularTransportBridgeTarget :
  _root_.InfoGeometry.GrandUnification.OperatorialConnesTransportSurface ℝ := by
  exact _root_.InfoGeometry.GrandUnification.operatorialConnesTransportSurface ℝ

/-- Compatibility readout for the operatorial modular transport theorem. -/
theorem constructModularTransportBridgeTarget :
    _root_.InfoGeometry.GrandUnification.OperatorialConnesTransportSurface ℝ :=
  modularTransportBridgeTarget

/-- Tomita--Gromov theorem stack on the currently proved operatorial surfaces. -/
theorem tomitaGromovBridgeTarget :
    _root_.InfoGeometry.GrandUnification.OperatorialConnesTransportSurface ℝ ∧
      AlgebraicSouriauTomitaTarget := by
  refine ⟨?_, ?_⟩
  · exact modularTransportBridgeTarget
  · exact constructAlgebraicSouriauTomitaTarget

/-- Constructor for the narrowed Tomita--Gromov endpoint from proved owner theorems. -/
theorem constructTomitaGromovBridgeTarget :
    _root_.InfoGeometry.GrandUnification.OperatorialConnesTransportSurface ℝ ∧
      AlgebraicSouriauTomitaTarget :=
  tomitaGromovBridgeTarget

end InfoGeometry.GrandUnification

end
