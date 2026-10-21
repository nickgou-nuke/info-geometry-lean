/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
import InfoGeometry.Thermo.OnsagerOperatorClosure
import InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms

/-!
# Finite directional Fréchet–BKM Onsager bridge

This owner proves a finite bridge from the existing directional second
Fréchet/log-partition readout to the abstract Onsager carrier.  The reversible
component is explicitly zero because no reversible response is inferred from
the BKM Hessian alone.
-/

noncomputable section

namespace InfoGeometry.Canonical.FrechetLeibnizOnsagerBridge

open InfoGeometry.Thermo.OnsagerClosure
open SouriauOnsagerBKM
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

noncomputable def faithfulDensityBKMOnsagerCasimirSystem
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) :
    OnsagerCasimirSystem (Operator n) :=
  { dissipative := D.bkmRealBilinForm hpow
    reversible := 0
    dissipative_symm := by
      intro A B
      exact (D.bkmRealBilinForm_symm hpow).eq A B
    reversible_skew := by
      intro A B
      simp
    dissipative_nonneg := by
      intro A
      exact D.kuboMoriPairing_self_re_nonneg A hpow }

@[simp] theorem faithfulDensityBKMOnsagerCasimirSystem_total_apply
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (A B : Operator n) :
    (faithfulDensityBKMOnsagerCasimirSystem D hpow).totalGenerator A B =
      D.bkmRealBilinForm hpow A B := by
  simp [faithfulDensityBKMOnsagerCasimirSystem,
    OnsagerCasimirSystem.totalGenerator]

theorem faithfulDensityBKMOnsagerCasimirSystem_entropy_nonnegative
    {n : ℕ} (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (A : Operator n) :
    0 ≤ (faithfulDensityBKMOnsagerCasimirSystem D hpow).totalGenerator A A := by
  exact (faithfulDensityBKMOnsagerCasimirSystem D hpow).entropy_production_nonneg A

theorem secondFDeriv_logPartition_eq_bkmOnsagerCasimir_centered
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) (hA : IsSelfAdjoint A) :
    (secondFDerivLogPartitionReadout H A B).re =
      (faithfulDensityBKMOnsagerCasimirSystem
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)).totalGenerator
          (centeredStatistic (faithfulGibbsDensity H hH hZ) A)
          (centeredStatistic (faithfulGibbsDensity H hH hZ) B) := by
  rw [faithfulDensityBKMOnsagerCasimirSystem_total_apply]
  exact secondFDeriv_logPartition_eq_bkmOnsagerForm_centered
    H hH hZ A B hA

end InfoGeometry.Canonical.FrechetLeibnizOnsagerBridge

end noncomputable section
