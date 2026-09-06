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

/-- The native operatorial Connes transport surface. -/
theorem operatorialConnesTransportSurface_proved :
  _root_.InfoGeometry.GrandUnification.OperatorialConnesTransportSurface ℝ := by
  exact _root_.InfoGeometry.GrandUnification.operatorialConnesTransportSurface ℝ

/-- Tomita--Gromov theorem stack on the proved operatorial surfaces. -/
theorem tomitaGromovBridge :
    _root_.InfoGeometry.GrandUnification.OperatorialConnesTransportSurface ℝ ∧
      (H1VolumeCocycleSurface ∧ MassieuVolumeSeparationSurface ∧ OperatorialConnesTransportSurface ℝ ∧ BoundaryWickAnomalySurface) := by
  refine ⟨?_, ?_⟩
  · exact operatorialConnesTransportSurface_proved
  · exact algebraicSouriauTomita_properties

end InfoGeometry.GrandUnification
