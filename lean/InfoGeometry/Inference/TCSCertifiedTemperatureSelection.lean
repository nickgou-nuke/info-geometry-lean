/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.CertifiedTemperatureSelection
import InfoGeometry.Inference.TCSPoissonModel

/-!
# Certified temperature selection for TCS Poisson energies

The susceptibility score is instantiated with the same Poisson Bregman energy
used by the TCS Gibbs weights. Fisher identifiability and good-volume evidence
remain explicit property inputs rather than inferred heuristics.
-/

namespace InfoGeometry.Inference

open scoped BigOperators
open FiniteGibbs

variable {Data : Type*} [Fintype Data] [Nonempty Data]

theorem exists_tcs_property_schedule_max_susceptibility
    (observed x liveTime : Data → ℝ)
    (hobs : ∀ i, 0 ≤ observed i)
    (p : TCSParameter x liveTime)
    (S : Finset ℝ) (P : ℝ → Prop) [DecidablePred P]
    (hP : (S.filter P).Nonempty)
    (hcertificate : ∀ ε, P ε →
      ∃ c : GibbsTemperatureCertificate
        (tcsFisherInformation
          (fun i => poissonWeight
            (tcsPoissonModel observed x liveTime hobs) p ε i)
          liveTime x), c.epsilon = ε) :
    ∃ ε ∈ S,
      ∃ c : GibbsTemperatureCertificate
        (tcsFisherInformation
          (fun i => poissonWeight
            (tcsPoissonModel observed x liveTime hobs) p ε i)
          liveTime x),
      c.epsilon = ε ∧ P ε ∧
        (∀ δ ∈ S, P δ →
          temperatureSusceptibility
              (fun i =>
                (tcsPoissonModel observed x liveTime hobs).energy i p) δ ≤
            temperatureSusceptibility
              (fun i =>
                (tcsPoissonModel observed x liveTime hobs).energy i p) ε) := by
  exact FiniteGibbs.exists_property_schedule_max_susceptibility
    (E := fun i =>
      (tcsPoissonModel observed x liveTime hobs).energy i p)
    (S := S) (P := P)
    (I := fun ε =>
      tcsFisherInformation
        (fun i => poissonWeight
          (tcsPoissonModel observed x liveTime hobs) p ε i)
        liveTime x)
    hP hcertificate

end InfoGeometry.Inference
