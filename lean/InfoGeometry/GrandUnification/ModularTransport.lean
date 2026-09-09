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

/-- Finite modular transport theorem from the owner finite Connes cocycle. -/
theorem modularTransportBridgeTarget :
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
                  φ ψ t j) i := by
  intro φ ψ s t
  exact
    _root_.InfoGeometry.Thermodynamics.FiniteConnesCocycle.finite_commuting_connes_cocycle_satisfies_cocycle
      φ ψ s t

/--
Compatibility readout for the finite modular transport theorem.
-/
theorem constructModularTransportBridgeTarget :
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
                    φ ψ t j) i :=
  modularTransportBridgeTarget

/--
Tomita--Gromov theorem stack, narrowed to the currently proved finite theorem
surface.
-/
theorem tomitaGromovBridgeTarget :
    (∀ (φ ψ : _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.FiniteTemperature (Fin 2))
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
                    φ ψ t j) i) ∧
      AlgebraicSouriauTomitaTarget := by
  exact ⟨modularTransportBridgeTarget, constructAlgebraicSouriauTomitaTarget⟩

/-- Constructor for the narrowed Tomita--Gromov endpoint from proved owner theorems. -/
theorem constructTomitaGromovBridgeTarget :
    (∀ (φ ψ : _root_.InfoGeometry.Thermodynamics.FiniteGibbsRelative.FiniteTemperature (Fin 2))
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
                    φ ψ t j) i) ∧
      AlgebraicSouriauTomitaTarget :=
  tomitaGromovBridgeTarget

end InfoGeometry.GrandUnification

end
