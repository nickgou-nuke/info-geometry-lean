/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.ParaKahler.ParaKahlerMetriplecticFisherClosure
import InfoGeometry.Thermo.CantorGibbsModularBridge

namespace InfoGeometry.ParaKahler.RapidityAngleApollonius

open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Thermo.BinaryEntropyMetriplectic
open InfoGeometry.Thermo.CantorGibbsModularBridge

noncomputable section

/-- The finite Gibbs coordinate, when identified with the doubled logistic
coordinate, makes the binary metriplectic entropy production equal to the
para-Kähler rapidity Hessian coefficient times the squared entropy force. -/
theorem localGibbs_entropyRate_eq_paraKahlerMetric
    (q r β ε : ℝ) (p : Set.Ioo (0 : ℝ) 1)
    (hp : p.1 = localWeightPlus β ε) :
    (system q r p).dS (system q r p).flow =
      (dikinRapidityMetric (β * ε / 2) / 8) * (logit p.1) ^ 2 := by
  rw [system_entropy_rate]
  rw [hp, localWeightPlus_eq_logistic]
  rw [dikinRapidityMetric_eq_eight_fisherExp_double]
  simp [fisherExp]
  apply Or.inl
  ring_nf

end
end InfoGeometry.ParaKahler.RapidityAngleApollonius
