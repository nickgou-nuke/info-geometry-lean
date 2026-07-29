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

structure GibbsTemperatureCertificate
    (I : Matrix (Fin 2) (Fin 2) ℝ) where
  epsilon : ℝ
  goodVolume : ℝ
  minimumGoodVolume : ℝ
  epsilon_pos : 0 < epsilon
  goodVolume_lower_bound : minimumGoodVolume ≤ goodVolume
  fisher : FisherInverseContract I

theorem GibbsTemperatureCertificate.temperature_positive
    {I : Matrix (Fin 2) (Fin 2) ℝ}
    (c : GibbsTemperatureCertificate I) :
    0 < c.epsilon :=
  c.epsilon_pos

theorem GibbsTemperatureCertificate.good_volume_admissible
    {I : Matrix (Fin 2) (Fin 2) ℝ}
    (c : GibbsTemperatureCertificate I) :
    c.minimumGoodVolume ≤ c.goodVolume :=
  c.goodVolume_lower_bound

theorem GibbsTemperatureCertificate.fisher_nonsingular
    {I : Matrix (Fin 2) (Fin 2) ℝ}
    (c : GibbsTemperatureCertificate I) :
    IsUnit I.det :=
  c.fisher.determinant_isUnit

end InfoGeometry.Inference
