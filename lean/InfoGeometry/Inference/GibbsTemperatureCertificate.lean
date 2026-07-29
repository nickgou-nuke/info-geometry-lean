/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FisherInverse

/-!
# Certified finite Gibbs temperature admissibility

This structure packages the conditions required before a temperature can be
used for a sensitivity report: positive temperature, sufficient normalized
good-fit volume, and a nonsingular positive-definite Fisher matrix.
-/

namespace InfoGeometry.Inference

abbrev GibbsTemperatureParameters :=
  ℝ × ℝ × ℝ

def GibbsTemperatureCertificate
    (I : Matrix (Fin 2) (Fin 2) ℝ) : Type _ :=
  {p : GibbsTemperatureParameters //
    0 < p.1 ∧ p.2.2 ≤ p.2.1 ∧ FisherInverseContract I}

namespace GibbsTemperatureCertificate

variable {I : Matrix (Fin 2) (Fin 2) ℝ}

def epsilon (c : GibbsTemperatureCertificate I) : ℝ :=
  c.1.1

def goodVolume (c : GibbsTemperatureCertificate I) : ℝ :=
  c.1.2.1

def minimumGoodVolume (c : GibbsTemperatureCertificate I) : ℝ :=
  c.1.2.2

def fisher (c : GibbsTemperatureCertificate I) : FisherInverseContract I :=
  c.2.2.2

def mk
    (epsilon goodVolume minimumGoodVolume : ℝ)
    (epsilon_pos : 0 < epsilon)
    (goodVolume_lower_bound : minimumGoodVolume ≤ goodVolume)
    (fisher : FisherInverseContract I) : GibbsTemperatureCertificate I :=
  ⟨(epsilon, goodVolume, minimumGoodVolume),
    ⟨epsilon_pos, goodVolume_lower_bound, fisher⟩⟩

end GibbsTemperatureCertificate

theorem GibbsTemperatureCertificate.temperature_positive
    {I : Matrix (Fin 2) (Fin 2) ℝ}
    (c : GibbsTemperatureCertificate I) :
    0 < c.epsilon := by
  simpa [GibbsTemperatureCertificate.epsilon] using c.2.1

theorem GibbsTemperatureCertificate.good_volume_admissible
    {I : Matrix (Fin 2) (Fin 2) ℝ}
    (c : GibbsTemperatureCertificate I) :
    c.minimumGoodVolume ≤ c.goodVolume := by
  simpa [GibbsTemperatureCertificate.minimumGoodVolume,
    GibbsTemperatureCertificate.goodVolume] using c.2.2.1

theorem GibbsTemperatureCertificate.fisher_nonsingular
    {I : Matrix (Fin 2) (Fin 2) ℝ}
    (c : GibbsTemperatureCertificate I) :
    IsUnit I.det :=
  (GibbsTemperatureCertificate.fisher c).determinant_isUnit

end InfoGeometry.Inference
