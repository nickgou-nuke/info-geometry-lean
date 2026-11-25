/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
import InfoGeometry.Lie.SO55GlobalConformalPrecursors

/-!
# Finite `Cl(1,1)` boundary transport

This owner records the kernel-checked part of the proposed finite Tomita lane:
the sewn Cantor boundary carries two involutions whose product is the split
clock axis.  It deliberately does not identify that algebraic clock with an
analytic modular flow or assert a KMS theorem without the corresponding
analytic hypotheses.
-/

noncomputable section

open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
open InfoGeometry.Lie.SO55GlobalConformalPrecursors

namespace InfoGeometry.Tomita.FiniteTomitaModularFlow

/-- A `Cl(1,1)` package on the completed sewn boundary carrier. -/
structure FiniteCl11
    (E : Type 0) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  J : H_lp E →L[ℝ] H_lp E
  ε : H_lp E →L[ℝ] H_lp E
  K : H_lp E →L[ℝ] H_lp E
  hJ_sq : J.comp J = ContinuousLinearMap.id ℝ (H_lp E)
  hε_sq : ε.comp ε = ContinuousLinearMap.id ℝ (H_lp E)
  hJ_ε_anticomm : J.comp ε = -(ε.comp J)
  hK_def : K = J.comp ε

/-- The canonical boundary `Cl(1,1)` package. -/
def canonicalCl11
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : FiniteCl11 E :=
  { J := J_lp_clm
    ε := epsilon_lp_clm
    K := (J_lp_clm (E := E)).comp (epsilon_lp_clm (E := E))
    hJ_sq := J_lp_clm_comp_self
    hε_sq := epsilon_lp_clm_comp_self
    hJ_ε_anticomm := J_lp_clm_anticomm_epsilon_lp_clm
    hK_def := rfl }

/-- The split clock operator associated with a `Cl(1,1)` package. -/
def clockOperator
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (cl : FiniteCl11 E) : H_lp E →L[ℝ] H_lp E := cl.K

/-- The modular swap component of a `Cl(1,1)` package. -/
def conjugationOperator
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (cl : FiniteCl11 E) : H_lp E →L[ℝ] H_lp E := cl.J

/-- The canonical package has the advertised `Cl(1,1)` relations. -/
theorem canonicalCl11_relations
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    let cl := canonicalCl11 (E := E)
    cl.J.comp cl.J = ContinuousLinearMap.id ℝ (H_lp E) ∧
      cl.ε.comp cl.ε = ContinuousLinearMap.id ℝ (H_lp E) ∧
      cl.J.comp cl.ε = -(cl.ε.comp cl.J) := by
  dsimp [canonicalCl11]
  exact ⟨J_lp_clm_comp_self, epsilon_lp_clm_comp_self,
    J_lp_clm_anticomm_epsilon_lp_clm⟩

/-- Conjugating the split clock by the swap reverses its sign. -/
theorem conjugation_clock_conjugation
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (cl : FiniteCl11 E) :
    (cl.J.comp cl.K).comp cl.J = -cl.K := by
  calc
    (cl.J.comp cl.K).comp cl.J =
        (cl.J.comp (cl.J.comp cl.ε)).comp cl.J := by rw [cl.hK_def]
    _ = ((cl.J.comp cl.J).comp cl.ε).comp cl.J := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = ((ContinuousLinearMap.id ℝ (H_lp E)).comp cl.ε).comp cl.J := by
      rw [cl.hJ_sq]
    _ = cl.ε.comp cl.J := by simp [ContinuousLinearMap.id_comp]
    _ = -(cl.J.comp cl.ε) := by
      rw [cl.hJ_ε_anticomm]
      simp
    _ = -cl.K := by rw [cl.hK_def]

/-- The split clock squares to minus the identity, as forced by the
`Cl(1,1)` anticommutation relation. -/
theorem clockOperator_sq_neg
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (cl : FiniteCl11 E) :
    cl.K.comp cl.K = -(ContinuousLinearMap.id ℝ (H_lp E)) := by
  have hεJ : cl.ε.comp cl.J = -(cl.J.comp cl.ε) := by
    rw [cl.hJ_ε_anticomm]
    simp
  calc
    cl.K.comp cl.K = (cl.J.comp cl.ε).comp (cl.J.comp cl.ε) := by rw [cl.hK_def]
    _ = (cl.J.comp (cl.ε.comp cl.J)).comp cl.ε := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = (cl.J.comp (-(cl.J.comp cl.ε))).comp cl.ε := by rw [hεJ]
    _ = -((cl.J.comp cl.J).comp (cl.ε.comp cl.ε)) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = -((ContinuousLinearMap.id ℝ (H_lp E)).comp
          (ContinuousLinearMap.id ℝ (H_lp E))) := by
      rw [cl.hJ_sq, cl.hε_sq]
    _ = -(ContinuousLinearMap.id ℝ (H_lp E)) := by
      simp

/-- The sewn canonical state is fixed by the modular swap. -/
theorem canonical_state_fixed :
    J_lp_clm (E := ℝ) canonicalCantorSewnState = canonicalCantorSewnState :=
  canonicalCantorSewnState_fixed

/-- The canonical sewn state has zero chiral expectation for every sewn operator. -/
theorem canonical_state_chiral_zero
    (B : H_lp ℝ →L[ℝ] H_lp ℝ)
    (hB : (J_lp_clm (E := ℝ)).comp
      (B.comp (J_lp_clm (E := ℝ))) = B) :
    inner ℝ canonicalCantorSewnState
      (((epsilon_lp_clm (E := ℝ)).comp B) canonicalCantorSewnState) = 0 :=
  canonicalCantorSewnState_chiral_zero B hB

/-- The general sewn-boundary anomaly cancellation theorem. -/
theorem sewn_boundary_anomaly_zero
    {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (B : H_lp E →L[ℝ] H_lp E)
    (hB : (J_lp_clm (E := E)).comp
      (B.comp (J_lp_clm (E := E))) = B)
    (ψ : H_lp E)
    (hψ : J_lp_clm (E := E) ψ = ψ) :
    inner ℝ ψ (((epsilon_lp_clm (E := E)).comp B) ψ) = 0 :=
  infinite_hilbert_sewn_chiral_expectation_zero B hB ψ hψ

/-- The explicit `SO(5,5)` boost owner supplies the compatible causal action. -/
theorem thermal_clock_boost_is_so55 (ξ : ℝ) :
    IsSO55GroupMatrix (so55Boost ξ) :=
  so55Boost_isSO55 ξ

end InfoGeometry.Tomita.FiniteTomitaModularFlow
