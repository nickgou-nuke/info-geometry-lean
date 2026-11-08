/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11PeirceOrbitColimit
import InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace

/-! Weighted Peirce readouts use the native normalized-trace cocone.
The boundary identity is algebraic and does not assert analytic KMS data. -/
noncomputable section
namespace InfoGeometry.Canonical.Cl11PeirceWeightTrace
open InfoGeometry.Clifford.Cl11TensorTower InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.OperatorAlgebra.TracialCARDensity
open Cl11TensorInductiveLimit Cl11TensorInductiveLimitTopologicalTrace
open CliffordCARAlgebraicTopologicalComparison PeirceWeightedTrace

def stageTracialFunctional (n : ℕ) : InfoGeometry.NCG.TracialFunctional ℝ (MatStage n) where
  toLinearMap := normalizedTraceLinear n
  cyclic' X Y := by
    change normalizedTrace n (X*Y) = normalizedTrace n (Y*X)
    unfold normalizedTrace
    rw [Matrix.trace_mul_comm]

theorem weighted_readback (n : ℕ) (a b : ℝ) (d B X : MatStage n) :
    normalizedTraceTopologicalColimitMap (algebraicToTopological
      (supportWeight a b (ofStage n d) (ofStage n B) * ofStage n X)) =
      normalizedTrace n (supportWeight a b d B * X) := by
  have hw : ofStage n (supportWeight a b d B) =
      supportWeight a b (ofStage n d) (ofStage n B) := by
    change ofStageAlgHom n (supportWeight a b d B) =
      supportWeight a b (ofStageAlgHom n d) (ofStageAlgHom n B)
    simp only [supportWeight, map_add, map_smul, map_mul]
  rw [← hw, ← map_mul, normalizedTraceTopologicalColimitMap_algebraic_stage]

theorem weighted_successor (n : ℕ) (a b : ℝ) (d B X : MatStage n) :
    normalizedTrace (n+1)
      (supportWeight a b (stageEmbed n d) (stageEmbed n B) * stageEmbed n X) =
      normalizedTrace n (supportWeight a b d B * X) := by
  have hw : stageEmbed n (supportWeight a b d B * X) =
      supportWeight a b (stageEmbed n d) (stageEmbed n B) * stageEmbed n X := by
    simp only [supportWeight, map_add, map_smul, map_mul]
  rw [← hw]
  exact cl11_normalizedTrace_one_step n _

theorem weighted_boundary_readback (n : ℕ) (a b : ℝ) (d B X : MatStage n)
    (hd : d*d=0) (hB : B*B=0) (hr : d*B*d=d) (hs : B*d*B=B) :
    a * normalizedTraceTopologicalColimitMap (algebraicToTopological
      (supportWeight a b (ofStage n d) (ofStage n B) * ofStage n (d*X))) =
    b * normalizedTraceTopologicalColimitMap (algebraicToTopological
      (supportWeight a b (ofStage n d) (ofStage n B) * ofStage n (X*d))) := by
  rw [weighted_readback, weighted_readback]
  exact (weighted_trace_boundary (stageTracialFunctional n) hd hB hr hs a b X).1

end InfoGeometry.Canonical.Cl11PeirceWeightTrace
