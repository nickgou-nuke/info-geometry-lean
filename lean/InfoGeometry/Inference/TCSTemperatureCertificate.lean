/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.GibbsTemperatureCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.TCSPoissonModel

/-!
# TCS Gibbs temperature certificate

This constructor connects the generic certificate to the physical TCS model.
The Fisher positive-definiteness witness remains an explicit assumption: the
preceding Fisher theory proves positive semidefiniteness, not identifiability.
-/

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data] [Nonempty Data]

noncomputable def tcsTemperatureCertificate
    (observed x liveTime : Data → ℝ)
    (hobs : ∀ i, 0 ≤ observed i)
    (p : TCSParameter x liveTime)
    (ε minimumGoodVolume goodVolume : ℝ)
    (hε : 0 < ε)
    (hgood : minimumGoodVolume ≤ goodVolume)
    (hF : FisherInverseContract
      (tcsFisherInformation
        (fun i => poissonWeight
          (tcsPoissonModel observed x liveTime hobs) p ε i)
        liveTime x)) :
    GibbsTemperatureCertificate
      (tcsFisherInformation
        (fun i => poissonWeight
          (tcsPoissonModel observed x liveTime hobs) p ε i)
        liveTime x) :=
  GibbsTemperatureCertificate.mk ε goodVolume minimumGoodVolume hε hgood hF

end InfoGeometry.Inference
