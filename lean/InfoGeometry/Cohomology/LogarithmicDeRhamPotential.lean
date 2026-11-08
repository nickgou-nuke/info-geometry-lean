/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
import InfoGeometry.ExponentialFamily.Analytic.Softmax
import InfoGeometry.Detector.AmariHessianDuality
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace InfoGeometry.Cohomology.LogarithmicDeRhamPotential

open InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
open InfoGeometry.Analytic
open InfoGeometry.Detector.AmariHessianDuality

inductive Archetype
  | logForm
  | logPotential
  | residue
  | fisherHessian
  | dilogarithm
  deriving DecidableEq, Repr

def precedes : Archetype → Archetype → Prop
  | .logForm, .logPotential => True
  | .logPotential, .residue => True
  | .residue, .fisherHessian => True
  | .fisherHessian, .dilogarithm => True
  | _, _ => False

theorem causal_chain :
    precedes .logForm .logPotential ∧
    precedes .logPotential .residue ∧
    precedes .residue .fisherHessian ∧
    precedes .fisherHessian .dilogarithm := by
  exact ⟨trivial, trivial, trivial, trivial⟩

noncomputable def logCoord (y : ℝ) : ℝ := Real.log y

theorem logCoord_dilation (c y : ℝ) (hc : 0 < c) (hy : 0 < y) :
    logCoord (c * y) = Real.log c + logCoord y := by
  simpa [logCoord] using Real.log_mul (ne_of_gt hc) (ne_of_gt hy)

theorem hasDerivAt_logCoord {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt logCoord (1 / y) y := by
  change HasDerivAt (fun z : ℝ => Real.log z) (1 / y) y
  simpa [one_div] using Real.hasDerivAt_log hy

theorem coordinate_log_reuses_owner {α : Type*} [Fintype α]
    (i : α) {x : Chart α} (hx : x i ≠ 0) :
    HasFDerivAt (coordinateLogPotential i)
      ((1 / x i) • coordinateCLM i) x :=
  hasFDerivAt_coordinateLogPotential i hx

theorem fisher_ceiling (p : ℝ) : p * (1 - p) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

theorem fisher_ceiling_reuses_owner (coefficient efficiency : ℝ) :
    fisher_metric coefficient efficiency ≤ 1 / 4 :=
  fisher_metric_le_quarter coefficient efficiency

theorem softmax_two_channel_partition_pos (x0 x1 : ℝ) :
    0 < Real.exp x0 + Real.exp x1 := by
  positivity

noncomputable def partitionZ (x0 x1 : ℝ) : ℝ :=
  Real.exp x0 + Real.exp x1

noncomputable def logPotential (x0 x1 : ℝ) : ℝ :=
  Real.log (partitionZ x0 x1)

noncomputable def softmaxP0 (x0 x1 : ℝ) : ℝ :=
  Real.exp x0 / partitionZ x0 x1

theorem partitionZ_pos (x0 x1 : ℝ) : 0 < partitionZ x0 x1 := by
  simpa [partitionZ] using softmax_two_channel_partition_pos x0 x1

theorem logPotential_derivative (x0 x1 : ℝ) :
    HasDerivAt (fun s => logPotential s x1) (softmaxP0 x0 x1) x0 := by
  dsimp [logPotential, softmaxP0, partitionZ]
  have h := (Real.hasDerivAt_exp x0).add
    (hasDerivAt_const x0 (Real.exp x1))
  have hlog := h.log (ne_of_gt (softmax_two_channel_partition_pos x0 x1))
  simpa using hlog

theorem softmaxP0_derivative (x0 x1 : ℝ) :
    HasDerivAt (fun s => softmaxP0 s x1)
      (softmaxP0 x0 x1 * (1 - softmaxP0 x0 x1)) x0 := by
  dsimp [softmaxP0, partitionZ]
  have hden : Real.exp x0 + Real.exp x1 ≠ 0 :=
    ne_of_gt (softmax_two_channel_partition_pos x0 x1)
  have h := (Real.hasDerivAt_exp x0).div
    ((Real.hasDerivAt_exp x0).add (hasDerivAt_const x0 (Real.exp x1))) hden
  convert h using 1 <;> simp only [Pi.add_apply] <;> field_simp [hden] <;> ring_nf

theorem softmax_two_channel_derivative (x0 x1 : ℝ) :
    HasDerivAt
      (fun s => Real.exp s / (Real.exp s + Real.exp x1))
      ((Real.exp x0 / (Real.exp x0 + Real.exp x1)) *
        (1 - Real.exp x0 / (Real.exp x0 + Real.exp x1))) x0 := by
  have hden : Real.exp x0 + Real.exp x1 ≠ 0 :=
    ne_of_gt (softmax_two_channel_partition_pos x0 x1)
  have h := (Real.hasDerivAt_exp x0).div
    ((Real.hasDerivAt_exp x0).add (hasDerivAt_const x0 (Real.exp x1))) hden
  convert h using 1 <;> simp only [Pi.add_apply] <;> field_simp [hden] <;> ring_nf

theorem logsumexp_derivative_reuses_owner
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (logSumExp w a) θ =
      softmaxMean (w := w) (a := a) hw θ :=
  deriv_logSumExp_eq_softmaxMean w a hw θ

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def archetypeOperatorWitness (P A C : B) : Archetype → B
  | .logForm => P
  | .logPotential => conePlus P A
  | .residue => genPhi P A C
  | .fisherHessian => genSig P A C
  | .dilogarithm => genV P A C

theorem logarithmic_de_rham_potential_operator_tetraktys
    {P : B} (hP : P * P = P) (A C : B) :
    archetypeOperatorWitness P A C .logForm *
      archetypeOperatorWitness P A C .logForm =
      archetypeOperatorWitness P A C .logForm ∧
    (archetypeOperatorWitness P A C .logPotential) ^ 2 = 0 ∧
    (archetypeOperatorWitness P A C .residue) ^ 2 =
      archetypeOperatorWitness P A C .dilogarithm ∧
    (archetypeOperatorWitness P A C .fisherHessian) ^ 2 -
      (archetypeOperatorWitness P A C .dilogarithm) ^ 2 = 0 := by
  dsimp only [archetypeOperatorWitness]
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C with
    ⟨hPlus, _, hPhiSq, _, _, _, _, _, _, _, hSigmaSq, _, _, _⟩
  refine ⟨hP, ?_, ?_, ?_⟩
  · simpa [pow_two] using hPlus
  · simpa [pow_two] using hPhiSq
  · simpa [pow_two] using sub_eq_zero.mpr hSigmaSq

end NonCommutativeOperatorRealization

end InfoGeometry.Cohomology.LogarithmicDeRhamPotential
