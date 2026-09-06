/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.TCSCertifiedTemperatureSelection
import InfoGeometry.Inference.TCSSensitivityCertificate

/-!
# End-to-end property TCS sensitivity selection

This theorem composes the finite Poisson temperature selector with the local
inverse-Fisher sensitivity report. It remains conditional on the experimental
property supplied for each admissible schedule point.
-/

namespace InfoGeometry.Inference

open scoped BigOperators
open FiniteGibbs

variable {Data : Type*} [Fintype Data] [Nonempty Data]

theorem exists_tcs_property_sensitivity_selection
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
                (tcsPoissonModel observed x liveTime hobs).energy i p) ε) ∧
        0 ≤ tcsCLocalStdDev
          (tcsFisherInformation
            (fun i => poissonWeight
              (tcsPoissonModel observed x liveTime hobs) p ε i)
            liveTime x) c ∧
        0 ≤ tcsKLocalStdDev
          (tcsFisherInformation
            (fun i => poissonWeight
              (tcsPoissonModel observed x liveTime hobs) p ε i)
            liveTime x) c := by
  obtain ⟨ε, hεS, c, hcε, hεP, hmax⟩ :=
    exists_tcs_property_schedule_max_susceptibility
      observed x liveTime hobs p S P hP hcertificate
  refine ⟨ε, hεS, c, hcε, hεP, hmax, ?_, ?_⟩
  · exact tcsCLocalStdDev_nonneg _ c
  · exact tcsKLocalStdDev_nonneg _ c

end InfoGeometry.Inference
