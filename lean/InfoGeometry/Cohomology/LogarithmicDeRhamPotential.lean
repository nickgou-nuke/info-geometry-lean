import InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
import InfoGeometry.ExponentialFamily.Analytic.Softmax
import InfoGeometry.Detector.AmariHessianDuality
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
  simpa [logCoord, one_div] using Real.hasDerivAt_log hy

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
  convert hlog using 1 <;> ring

theorem softmaxP0_derivative (x0 x1 : ℝ) :
    HasDerivAt (fun s => softmaxP0 s x1)
      (softmaxP0 x0 x1 * (1 - softmaxP0 x0 x1)) x0 := by
  dsimp [softmaxP0, partitionZ]
  have hden : Real.exp x0 + Real.exp x1 ≠ 0 :=
    ne_of_gt (softmax_two_channel_partition_pos x0 x1)
  have h := (Real.hasDerivAt_exp x0).div
    ((Real.hasDerivAt_exp x0).add (hasDerivAt_const x0 (Real.exp x1))) hden
  convert h using 1 <;> field_simp <;> ring

theorem softmax_two_channel_derivative (x0 x1 : ℝ) :
    HasDerivAt
      (fun s => Real.exp s / (Real.exp s + Real.exp x1))
      ((Real.exp x0 / (Real.exp x0 + Real.exp x1)) *
        (1 - Real.exp x0 / (Real.exp x0 + Real.exp x1))) x0 := by
  have hden : Real.exp x0 + Real.exp x1 ≠ 0 :=
    ne_of_gt (softmax_two_channel_partition_pos x0 x1)
  have h := (Real.hasDerivAt_exp x0).div
    ((Real.hasDerivAt_exp x0).add (hasDerivAt_const x0 (Real.exp x1))) hden
  convert h using 1 <;> field_simp <;> ring

theorem logsumexp_derivative_reuses_owner
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 < w i) (θ : ℝ) :
    deriv (logSumExp w a) θ =
      softmaxMean (w := w) (a := a) hw θ :=
  deriv_logSumExp_eq_softmaxMean w a hw θ

end InfoGeometry.Cohomology.LogarithmicDeRhamPotential
