/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.AdmissibleTemperatureSelection
import InfoGeometry.Inference.GibbsTemperatureCertificate
import InfoGeometry.Inference.GibbsTemperatureSusceptibility

/-!
# Certified finite Gibbs temperature selection

This is the composition theorem for the selection layer: maximizing
temperature susceptibility over an admissible finite schedule preserves the
property attached to every admissible candidate.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators

variable {Data : Type*} [Fintype Data] [Nonempty Data]

theorem exists_property_schedule_max_susceptibility
    (E : Data → ℝ) (S : Finset ℝ) (P : ℝ → Prop) [DecidablePred P]
    (I : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hP : (S.filter P).Nonempty)
    (hcertificate : ∀ ε, P ε →
      ∃ c : GibbsTemperatureCertificate (I ε), c.epsilon = ε) :
    ∃ ε ∈ S, ∃ c : GibbsTemperatureCertificate (I ε),
      c.epsilon = ε ∧ P ε ∧
        (∀ δ ∈ S, P δ →
          temperatureSusceptibility E δ ≤ temperatureSusceptibility E ε) := by
  obtain ⟨ε, hεS, hεP, hmax⟩ :=
    exists_filtered_schedule_max S P
      (temperatureSusceptibility E) hP
  obtain ⟨c, hc⟩ := hcertificate ε hεP
  exact ⟨ε, hεS, c, hc, hεP, hmax⟩

end InfoGeometry.Inference.FiniteGibbs
