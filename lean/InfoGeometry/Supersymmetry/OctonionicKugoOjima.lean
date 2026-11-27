/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RadonNikodymFisherMetricBridge
import InfoGeometry.Algebra.SplitOctonionColeFurySpinorBridge

noncomputable section

namespace InfoGeometry.Supersymmetry.OctonionicKugoOjima

open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Algebra.ColeFurySpinorBridge
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- 1. БРСТ оператор Q_B, произтичащ от симетриите на разцепените октониони. -/
def brstCharge (X A : EndH) : EndH :=
  transportCommutator X A

/-- 
2. Критерият на Куго-Оджима за конфайнмънт на цвета.
   Физическият безцветен вакуум се дефинира от състоянията, отразени обратно от бариерата.
   Алгебрично това означава, че двойният комутатор (Хесианът) изчезва върху вакуума.
-/
def kugoOjimaConfinementCondition (ω : EndH →L[ℝ] ℝ) (X A : EndH) : Prop :=
  ω (transportCommutator X (brstCharge X A)) = 0

/-- 
**Finite readout theorem**:
an explicit vanishing Hessian readout is sufficient for the
Kugo--Ojima confinement condition.  No octonion-to-spinor representation is
claimed here; that representation requires a separate, nonzero owner.
-/
@[rep_depth transport]
theorem kugoOjima_confinement_of_hessian_barrier
    (ω : EndH →L[ℝ] ℝ) (X A : EndH)
    (hHessian : deriv (fun t : ℝ => deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t) 0 =
                ω (transportCommutator X (transportCommutator X A)))
    (hBarrier : deriv (fun t : ℝ => deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t) 0 = 0) :
    kugoOjimaConfinementCondition ω X A := by
  dsimp [kugoOjimaConfinementCondition, brstCharge]
  rw [← hHessian, hBarrier]

omit [CompleteSpace E] in
/-- The Heisenberg commutator is additive in the observable slot. -/
private theorem transportCommutator_add_right (H A B : EndH) :
    transportCommutator H (A + B) = transportCommutator H A + transportCommutator H B := by
  apply ContinuousLinearMap.ext
  intro x
  simp [transportCommutator, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

omit [CompleteSpace E] in
/-- The algebraic Kugo--Ojima readout is additive in the observable: if two
observables satisfy the Hessian-barrier condition, so does their sum.  This is
a structural closure property of the confinement readout, not a physical
confinement theorem. -/
theorem kugoOjimaConfinementCondition_add (ω : EndH →L[ℝ] ℝ) (X A B : EndH)
    (hA : kugoOjimaConfinementCondition ω X A)
    (hB : kugoOjimaConfinementCondition ω X B) :
    kugoOjimaConfinementCondition ω X (A + B) := by
  dsimp [kugoOjimaConfinementCondition, brstCharge] at hA hB ⊢
  rw [transportCommutator_add_right]
  rw [transportCommutator_add_right]
  simp [hA, hB]

omit [CompleteSpace E] in
/-- A vanishing BRST variation satisfies the confinement readout for any
functional; the nontrivial content of the criterion is therefore carried by
genuinely noncommuting observables. -/
theorem kugoOjimaConfinementCondition_of_brst_zero (ω : EndH →L[ℝ] ℝ) (X A : EndH)
    (h : brstCharge X A = 0) :
    kugoOjimaConfinementCondition ω X A := by
  dsimp [kugoOjimaConfinementCondition]
  rw [h]
  simp [transportCommutator]

end InfoGeometry.Supersymmetry.OctonionicKugoOjima
