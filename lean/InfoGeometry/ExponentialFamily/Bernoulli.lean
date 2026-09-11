import InfoGeometry.ExponentialFamily.Class
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Canonical.Triality
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace InfoGeometry.ExponentialFamily.Bernoulli

open InfoGeometry.Convex
open InfoGeometry.Canonical.Triality

/-- Bernoulli log-partition function: ψ(η) = log(1 + exp η). -/
noncomputable def logPartition (η : ℝ) : ℝ :=
  Real.log (1 + Real.exp η)

/-- The Bernoulli dual map is the expectation parameter: p = exp(η) / (1 + exp(η)). -/
lemma deriv_logPartition (η : ℝ) :
    deriv logPartition η = Real.exp η / (1 + Real.exp η) := by
  have hbase : HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp η) η := by
    simpa using (Real.hasDerivAt_exp η).const_add 1
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + Real.exp y))
      (Real.exp η / (1 + Real.exp η)) η := by
    apply hbase.log
    linarith [Real.exp_pos η]
  simpa [logPartition] using hlog.deriv

/-- Bernoulli family as a 1D Hessian Geometry. -/
noncomputable def bernoulliHessianGeometry : HessianGeometry1D where
  potential := logPartition

/-- The metric of the Bernoulli family is the variance: p(1-p). -/
@[blueprint "thm:bernoulli-fisher-metric"]
lemma bernoulli_metric (η : ℝ) :
    bernoulliHessianGeometry.metric η = (Real.exp η) / (1 + Real.exp η)^2 := by
  unfold HessianGeometry1D.metric bernoulliHessianGeometry
  have hfun : deriv logPartition = fun x => Real.exp x / (1 + Real.exp x) := by
    funext x
    simpa using deriv_logPartition x
  rw [hfun]
  have h_pos : (1 + Real.exp η) ≠ 0 := by linarith [Real.exp_pos η]
  have hnum : HasDerivAt (fun x : ℝ => Real.exp x) (Real.exp η) η := Real.hasDerivAt_exp η
  have hden : HasDerivAt (fun x : ℝ => 1 + Real.exp x) (Real.exp η) η := by
    simpa using (Real.hasDerivAt_exp η).const_add 1
  have hquot :
      HasDerivAt (fun x : ℝ => Real.exp x / (1 + Real.exp x))
        ((Real.exp η * (1 + Real.exp η) - Real.exp η * Real.exp η) / (1 + Real.exp η) ^ 2) η :=
    hnum.div hden h_pos
  have hquot' :
      HasDerivAt (fun x : ℝ => Real.exp x / (1 + Real.exp x))
        (Real.exp η / (1 + Real.exp η) ^ 2) η := by
    convert hquot using 1
    ring
  simpa using hquot'.deriv

/-- 
The Bernoulli Bregman divergence is the KL-divergence between two distributions.
D(η₁, η₂) = log(1 + exp η₁) - log(1 + exp η₂) - σ(η₂)(η₁ - η₂).
-/
@[blueprint "thm:bernoulli-kl-divergence"]
theorem bernoulli_divergence_eq_kl (η₁ η₂ : ℝ) :
    bernoulliHessianGeometry.divergence η₁ η₂ = 
      logPartition η₁ - logPartition η₂ - (Real.exp η₂ / (1 + Real.exp η₂)) * (η₁ - η₂) := by
  unfold HessianGeometry1D.divergence HessianGeometry1D.dualMap bernoulliHessianGeometry
  rw [deriv_logPartition]

/-- 
Bregman divergence instance for the Bernoulli family.
Maps Bernoulli natural parameters to expectation parameters.
-/
noncomputable instance : BregmanDivergence ℝ ℝ :=
  { D := fun η₁ η₂ => bernoulliHessianGeometry.divergence η₁ η₂ }

/-- Bernoulli as a Triadic Core for Attention. -/
noncomputable def bernoulliTriadicCore : TriadicCore ℝ ℝ ℝ :=
  bregmanTriadicCore (fun η₁ η₂ => η₁ + η₂)

end InfoGeometry.ExponentialFamily.Bernoulli
