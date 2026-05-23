import InfoGeometry.GrandUnification.AlgebraicSouriauTomita
import InfoGeometry.Thermodynamics.FiniteConnesCocycle

/-!
# Modular transport, theorem-stack version

This module removes the former data-packet version of the grand modular
transport bridge.  It proves only the finite commuting Cartan transport surface
that is already owned by `InfoGeometry.Thermodynamics.FiniteConnesCocycle`.

What this module proves:

* the finite unitary Connes phase satisfies the scalar cocycle law with the
  explicit scalar reference modular action;
* the corrected Souriau--Tomita roadmap target is available as a theorem-stack
  conjunction.

What this module does not prove:

* full Tomita--Takesaki theory for von Neumann algebras;
* analytic Connes cocycle support/faithfulness/partial-isometry conditions;
* Gromov, Berry, Perelman, or spectral-normalization comparison theorems.
-/

noncomputable section

namespace InfoGeometry.GrandUnification

/--
Finite modular transport target.

This is intentionally a proposition, not a packet of supplied data.
-/
def ModularTransportBridgeTarget : Prop :=
  ∀ (φ ψ : _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.FiniteTemperature (Fin 2))
      (s t : ℝ),
    (fun i =>
        _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
          φ ψ (s + t) i) =
      fun i =>
        _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
          φ ψ s i *
          _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteScalarReferenceModularAction
            φ s
              (fun j =>
                _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finiteCommutingConnesPhaseOfStates
                  φ ψ t j) i

/--
Constructor for the finite modular transport target.

No external transport data are accepted; the proof delegates to the owner
finite Connes theorem.
-/
theorem constructModularTransportBridgeTarget :
    ModularTransportBridgeTarget := by
  intro φ ψ s t
  exact
    _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finite_commuting_connes_cocycle_satisfies_cocycle_law
      φ ψ s t

/--
Tomita--Gromov bridge target, narrowed to the currently proved finite theorem
stack.

The name is retained as a public roadmap endpoint, but no Gromov/spectral
comparison data are accepted here.  Those remain future theorem surfaces.
-/
def TomitaGromovBridgeTarget : Prop :=
  ModularTransportBridgeTarget ∧ AlgebraicSouriauTomitaTarget

/-- Constructor for the narrowed Tomita--Gromov endpoint from proved owner theorems. -/
theorem constructTomitaGromovBridgeTarget :
    TomitaGromovBridgeTarget := by
  exact ⟨constructModularTransportBridgeTarget, constructAlgebraicSouriauTomitaTarget⟩

end InfoGeometry.GrandUnification

end
