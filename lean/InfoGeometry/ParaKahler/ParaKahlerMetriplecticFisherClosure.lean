/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.ParaKahler.RapidityAngleHessianClosure
import InfoGeometry.Canonical.AmariBinarySimplexBridge
import InfoGeometry.Thermo.BinaryEntropyMetriplectic

namespace InfoGeometry.ParaKahler.RapidityAngleApollonius

open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Thermo.BinaryEntropyMetriplectic

noncomputable section

/-- The para-Kähler rapidity Hessian is the binary Fisher mobility in the
    doubled logistic coordinate, with the exact normalization induced by
    `q = 2 p - 1`. -/
theorem dikinRapidityMetric_eq_eight_fisherExp_double (χ : ℝ) :
    dikinRapidityMetric χ = 8 * fisherExp (2 * χ) := by
  have hpol :=
    InfoGeometry.Analysis.BipolarCayleyOccupation.real_polarization_eq_tanh (2 * χ)
  have heq : logistic (2 * χ) =
      InfoGeometry.Analysis.BipolarCrossRatioLog.logistic (2 * χ) := by
    rfl
  have hlogistic : 2 * logistic (2 * χ) - 1 = Real.tanh χ := by
    rw [heq]
    convert hpol using 1
    · ring_nf
  unfold dikinRapidityMetric souriauSignature fisherExp
  have hprod :
      logistic (2 * χ) * (1 - logistic (2 * χ)) =
        (1 - (Real.tanh χ) ^ 2) / 4 := by
    calc
      logistic (2 * χ) * (1 - logistic (2 * χ)) =
          (1 - (2 * logistic (2 * χ) - 1) ^ 2) / 4 := by ring
      _ = (1 - (Real.tanh χ) ^ 2) / 4 := by rw [hlogistic]
  rw [hprod]
  ring

/-- The concrete binary metriplectic mobility has the para-Kähler Hessian
    coefficient after the doubled logistic reparameterization. -/
theorem binaryEntropyMobility_at_doubled_logistic (χ : ℝ)
    (α : InfoGeometry.Thermo.GenericMetriplecticFlow.Covector
      InfoGeometry.Thermo.BinaryEntropyMetriplectic.V) :
    InfoGeometry.Thermo.BinaryEntropyMetriplectic.mobility (logistic (2 * χ)) α =
      (dikinRapidityMetric χ / 8 * α (InfoGeometry.Thermo.BinaryEntropyMetriplectic.e 2)) •
        InfoGeometry.Thermo.BinaryEntropyMetriplectic.e 2 := by
  rw [dikinRapidityMetric_eq_eight_fisherExp_double]
  simp [InfoGeometry.Thermo.BinaryEntropyMetriplectic.mobility, fisherExp]

end
end InfoGeometry.ParaKahler.RapidityAngleApollonius
