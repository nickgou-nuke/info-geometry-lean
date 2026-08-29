/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.LightCone.ApolloniusCylinder

namespace InfoGeometry.Canonical

open InfoGeometry.LightCone.ApolloniusCylinder Matrix Real

/-- 🏆 GRAND CANONICAL CAPSTONE: Apollonian Cylinder Light-Cone Metric Factorization -/
theorem grand_canonical_lightcone_factorization_synthesis
    (χ θ du dv : ℝ) :
    (fromLightCone (χ + θ) (χ - θ) = (χ, θ)) ∧
    (toLightCone ((du + dv) / 2) ((du - dv) / 2) = (du, dv)) ∧
    (metricIntervalRapidityAngle ((du + dv) / 2) ((du - dv) / 2) = metricIntervalLightCone du dv) ∧
    (metricIntervalLightCone (χ + θ) (χ - θ) = metricIntervalRapidityAngle χ θ) ∧
    (jacobianLightConeToRapidity.det = -1 / 2) ∧
    (lightConeMetricTensor 0 0 = 0 ∧ lightConeMetricTensor 1 1 = 0) :=
  grand_lightcone_factorization_synthesis χ θ du dv

end InfoGeometry.Canonical
