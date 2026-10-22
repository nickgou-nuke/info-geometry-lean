/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.MassSpectrometry.MultiEnergyIdentifiability
import InfoGeometry.MassSpectrometry.ChemicalGraph
import InfoGeometry.MassSpectrometry.VerifiedInferenceArchitecture

/-!
# Molecular multi-energy inverse problem

This adapter specializes the abstract observational quotient to the actual
mass-spectrometry spectrum and collision-condition carriers. Any proposed
chemical equivalence must be supplied explicitly, as must invariance and
separation of the physical forward simulator.
-/

namespace InfoGeometry.MassSpectrometry

/-- An energy-indexed forward simulator from a labelled molecular graph to
the existing finite mass-spectrometry observation carrier. -/
abbrev MolecularSpectralForwardModel (atoms peaks : ℕ) :=
  MultiEnergyForwardModel (MolecularGraph atoms) CollisionCondition (Spectrum peaks)

/-- Wrap an ordinary forward spectrum simulator into the generic model. -/
def molecularForwardModel {atoms peaks : ℕ}
    (simulate : CollisionCondition → MolecularGraph atoms → Spectrum peaks) :
    MolecularSpectralForwardModel atoms peaks :=
  ⟨simulate⟩

/-- The spectra predicted by one molecule at all collision conditions. -/
def molecularMultiEnergyObservation {atoms peaks : ℕ}
    (F : MolecularSpectralForwardModel atoms peaks) (G : MolecularGraph atoms) :
    MultiEnergyObservation peaks where
  spectrumAt := fun e => F.observe e G

/-- Matching all multi-energy observations is exactly observational equivalence. -/
theorem molecular_observation_eq_iff {atoms peaks : ℕ}
    (F : MolecularSpectralForwardModel atoms peaks)
    (G H : MolecularGraph atoms) :
    molecularMultiEnergyObservation F G =
      molecularMultiEnergyObservation F H ↔
        F.ObservationallyEquivalent G H := by
  constructor
  · intro h e
    exact congrFun (congrArg MultiEnergyObservation.spectrumAt h) e
  · intro h
    change MultiEnergyObservation.mk (fun e => F.observe e G) =
      MultiEnergyObservation.mk (fun e => F.observe e H)
    exact congrArg MultiEnergyObservation.mk (by
      funext e
      exact h e)

end InfoGeometry.MassSpectrometry
