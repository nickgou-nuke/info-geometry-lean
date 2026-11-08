/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfigurationResolvent
import InfoGeometry.Physics.NuclearThreeConfigurationDoubledAnalytic
import InfoGeometry.Physics.NuclearEffectiveObservables
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Real analytic graph embeddings and two-endpoint effective operators

The actual graph map inherits real analyticity from its complementary
resolvent and its proved Feshbach wave identity. Rectangular composition and
the real adjoint then transport analyticity to the existing effective
operator and Gram operator. The two energy arguments and sector parameters
remain independent; their respective complementary poles are excluded.
All analyticity statements use Mathlib's native `AnalyticOnNhd ℝ`.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationAnalytic

open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearThreeConfigurationResolvent
open InfoGeometry.Physics.NuclearThreeConfigurationDual
open InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction
open InfoGeometry.Physics.NuclearThreeConfigurationDoubledAnalytic
open InfoGeometry.Physics.NuclearEffectiveObservables

section Composition

variable {D X Y Z : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Composition of analytic families of rectangular real bounded maps. -/
theorem analyticAt_operator_comp {A : D → Y →L[ℝ] Z} {B : D → X →L[ℝ] Y}
    {p : D} (hA : AnalyticAt ℝ A p) (hB : AnalyticAt ℝ B p) :
    AnalyticAt ℝ (fun x => (A x).comp (B x)) p := by
  simpa only [ContinuousLinearMap.compL_apply] using
    ((ContinuousLinearMap.compL ℝ X Y Z).analyticAt_bilinear (A p, B p)).comp₂ hA hB

end Composition

section Adjoint

variable {D X Y : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The adjoint is real linear and continuous on these real operator spaces. -/
theorem analyticAt_real_adjoint {A : D → X →L[ℝ] Y} {p : D}
    (hA : AnalyticAt ℝ A p) :
    AnalyticAt ℝ (fun x => (A x).adjoint) p := by
  let adj : (X →L[ℝ] Y) ≃ₗᵢ[ℝ] (Y →L[ℝ] X) := ContinuousLinearMap.adjoint
  exact (adj.analyticAt (A p)).comp hA

end Adjoint

section EffectiveOperators

variable {D Mi Mf Hi Hf : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Mi] [InnerProductSpace ℝ Mi] [CompleteSpace Mi]
variable [NormedAddCommGroup Mf] [InnerProductSpace ℝ Mf] [CompleteSpace Mf]
variable [NormedAddCommGroup Hi] [InnerProductSpace ℝ Hi] [CompleteSpace Hi]
variable [NormedAddCommGroup Hf] [InnerProductSpace ℝ Hf] [CompleteSpace Hf]

/-- The owned real effective operator preserves analyticity of both embeddings. -/
theorem analyticAt_effectiveOperator
    {Ωi : D → Mi →L[ℝ] Hi} {Ωf : D → Mf →L[ℝ] Hf}
    (O : Hi →L[ℝ] Hf) {p : D}
    (hi : AnalyticAt ℝ Ωi p) (hf : AnalyticAt ℝ Ωf p) :
    AnalyticAt ℝ (fun x => effectiveOperator (Ωi x) (Ωf x) O) p :=
  analyticAt_operator_comp (analyticAt_real_adjoint hf)
    (analyticAt_operator_comp analyticAt_const hi)

end EffectiveOperators

/-- Analyticity comes from the actual supported resolvent, through the wave map. -/
theorem analyticOnNhd_graphMap (c g : ℝ) :
    AnalyticOnNhd ℝ (graphMap c g) {E : ℝ | E ≠ c} := by
  intro E hE
  have hR := analyticOnNhd_resolvent c E hE
  have hW : AnalyticAt ℝ
      (fun e : ℝ => NuclearRealKreinFeshbach.waveOperator projection
        (hamiltonian 0 c g) (resolvent c e)) E :=
    analyticAt_const.add ((hR.mul analyticAt_const).mul analyticAt_const)
  have hG := analyticAt_operator_comp hW
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => inclusion) E)
  simpa only [← graphMap_eq_waveOperator] using hG

/-- The positive induced metric is real analytic on the same energy domain. -/
theorem analyticOnNhd_normMetric (c g : ℝ) :
    AnalyticOnNhd ℝ (fun E => normMetric (graphMap c g E))
      {E : ℝ | E ≠ c} := by
  intro E hE
  have hG := analyticOnNhd_graphMap c g E hE
  exact analyticAt_operator_comp (analyticAt_real_adjoint hG) hG

/-- Independent initial/final sectors and energies share no pole assumption. -/
theorem analyticOnNhd_twoEndpoint_effectiveOperator (ci gi cf gf : ℝ)
    (O : ConfigurationSpace →L[ℝ] ConfigurationSpace) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ => effectiveOperator
        (graphMap ci gi p.1) (graphMap cf gf p.2) O)
      {p : ℝ × ℝ | p.1 ≠ ci ∧ p.2 ≠ cf} := by
  intro p hp
  have hi : AnalyticAt ℝ (fun z : ℝ × ℝ => graphMap ci gi z.1) p :=
    (analyticOnNhd_graphMap ci gi p.1 hp.1).comp analyticAt_fst
  have hf : AnalyticAt ℝ (fun z : ℝ × ℝ => graphMap cf gf z.2) p :=
    (analyticOnNhd_graphMap cf gf p.2 hp.2).comp analyticAt_snd
  exact analyticAt_effectiveOperator O hi hf

/-- The native doubled graph uses the actual doubled complementary inverse. -/
theorem analyticOnNhd_doubledGraphMap (c g : ℝ) :
    AnalyticOnNhd ℝ (doubledGraphMap c g) {E : ℝ | E ≠ c} := by
  intro E hE
  have hR := analyticOnNhd_doubledResolvent c E hE
  have hW : AnalyticAt ℝ
      (fun e : ℝ => NuclearRealKreinFeshbach.waveOperator doubledProjection
        (doubledHamiltonian 0 c g) (doubledResolvent c e)) E :=
    analyticAt_const.add ((hR.mul analyticAt_const).mul analyticAt_const)
  have hG := analyticAt_operator_comp hW
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => doubledInclusion) E)
  simpa only [← doubledGraphMap_eq_waveOperator] using hG

theorem analyticOnNhd_doubledNormMetric (c g : ℝ) :
    AnalyticOnNhd ℝ (fun E => normMetric (doubledGraphMap c g E))
      {E : ℝ | E ≠ c} := by
  intro E hE
  have hG := analyticOnNhd_doubledGraphMap c g E hE
  exact analyticAt_operator_comp (analyticAt_real_adjoint hG) hG

/-- Joint real analyticity for the actual two-endpoint doubled observable. -/
theorem analyticOnNhd_twoEndpoint_doubledEffectiveOperator (ci gi cf gf : ℝ)
    (O : DoubledCarrier →L[ℝ] DoubledCarrier) :
    AnalyticOnNhd ℝ
      (fun p : ℝ × ℝ => effectiveOperator
        (doubledGraphMap ci gi p.1) (doubledGraphMap cf gf p.2) O)
      {p : ℝ × ℝ | p.1 ≠ ci ∧ p.2 ≠ cf} := by
  intro p hp
  have hi : AnalyticAt ℝ (fun z : ℝ × ℝ => doubledGraphMap ci gi z.1) p :=
    (analyticOnNhd_doubledGraphMap ci gi p.1 hp.1).comp analyticAt_fst
  have hf : AnalyticAt ℝ (fun z : ℝ × ℝ => doubledGraphMap cf gf z.2) p :=
    (analyticOnNhd_doubledGraphMap cf gf p.2 hp.2).comp analyticAt_snd
  exact analyticAt_effectiveOperator O hi hf

end InfoGeometry.Physics.NuclearThreeConfigurationAnalytic
