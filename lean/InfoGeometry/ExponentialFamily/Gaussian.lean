import InfoGeometry.ExponentialFamily.Class
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Canonical.Triality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace InfoGeometry.ExponentialFamily.Gaussian

open InfoGeometry.Convex
open InfoGeometry.Canonical.Triality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 
Fixed-covariance Multivariate Gaussian Family.
The log-partition function is quadratic: ψ(η) = 1/2 <η, Σ η>.
-/
structure GaussianFamily (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  sigma : E →L[ℝ] E
  sigma_pos : ∀ x, x ≠ 0 → 0 < inner ℝ x (sigma x)
  sigma_symm : IsSelfAdjoint sigma

namespace GaussianFamily

variable (G : GaussianFamily E)

/-- Log-partition function for the Gaussian family. -/
noncomputable def logPartition (η : E) : ℝ :=
  (1/2 : ℝ) * inner ℝ η (G.sigma η)

/-- The gradient of the log-partition is the expectation parameter μ = Σ η. -/
lemma hasFDerivAt_logPartition (η : E) :
    HasFDerivAt G.logPartition (InnerProductSpace.toDual ℝ E (G.sigma η)) η := by
  unfold logPartition
  have h_id : HasFDerivAt (fun x : E => x) (1 : E →L[ℝ] E) η := by
    simpa using (hasFDerivAt_id η)
  have h_sigma : HasFDerivAt (fun x : E => G.sigma x) G.sigma η := G.sigma.hasFDerivAt
  have h_inner :
      HasFDerivAt (fun x : E => inner ℝ x (G.sigma x))
        ((fderivInnerCLM ℝ (η, G.sigma η)).comp ((1 : E →L[ℝ] E).prod G.sigma)) η :=
    h_id.inner ℝ h_sigma
  convert h_inner.const_smul (1/2 : ℝ) using 1
  · ext v
    have hsymm : inner ℝ η (G.sigma v) = inner ℝ v (G.sigma η) := by
      simpa [real_inner_comm] using (G.sigma_symm.isSymmetric η v).symm
    have hcomm : inner ℝ (G.sigma η) v = inner ℝ v (G.sigma η) := by
      simp [real_inner_comm]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
    simp [hsymm, hcomm, InnerProductSpace.toDual_apply_apply]
    ring_nf

/-- Non-negativity of the Gaussian Bregman form in primal coordinates. -/
lemma divergence_form_nonneg (η₁ η₂ : E) :
    0 ≤ G.logPartition η₁ - G.logPartition η₂ - inner ℝ (G.sigma η₂) (η₁ - η₂) := by
  have hform :
      G.logPartition η₁ - G.logPartition η₂ - inner ℝ (G.sigma η₂) (η₁ - η₂)
        = (1 / 2 : ℝ) * inner ℝ (η₁ - η₂) (G.sigma (η₁ - η₂)) := by
    unfold logPartition
    simp [inner_sub_left, inner_sub_right, map_sub]
    have hcross : inner ℝ η₁ (G.sigma η₂) = inner ℝ η₂ (G.sigma η₁) := by
      calc
        inner ℝ η₁ (G.sigma η₂) = inner ℝ (G.sigma η₁) η₂ := by
          simpa using (G.sigma_symm.isSymmetric η₁ η₂).symm
        _ = inner ℝ η₂ (G.sigma η₁) := by simp [real_inner_comm]
    have hcross' : inner ℝ (G.sigma η₂) η₁ = inner ℝ η₂ (G.sigma η₁) := by
      calc
        inner ℝ (G.sigma η₂) η₁ = inner ℝ η₁ (G.sigma η₂) := by simp [real_inner_comm]
        _ = inner ℝ η₂ (G.sigma η₁) := hcross
    have hdiag : inner ℝ (G.sigma η₂) η₂ = inner ℝ η₂ (G.sigma η₂) := by
      simp [real_inner_comm]
    rw [hcross, hcross', hdiag]
    ring_nf
  rw [hform]
  by_cases hzero : η₁ - η₂ = 0
  · simp [hzero]
  · have hpos : 0 < inner ℝ (η₁ - η₂) (G.sigma (η₁ - η₂)) :=
      G.sigma_pos (η₁ - η₂) hzero
    nlinarith

/-- Gaussian family as a Multivariate Hessian Geometry. -/
noncomputable def hessianGeometry : HessianGeometry E where
  potential := G.logPartition
  grad := G.sigma
  has_gradient := G.hasFDerivAt_logPartition
  divergence_form_nonneg := G.divergence_form_nonneg

/-- The Bregman divergence of the Gaussian family is the squared Mahalanobis distance. -/
@[blueprint "thm:gaussian-mahalanobis-divergence"]
theorem divergence_eq_mahalanobis (η₁ η₂ : E) :
    G.hessianGeometry.divergence η₁ η₂ = 
      (1/2 : ℝ) * inner ℝ (η₁ - η₂) (G.sigma (η₁ - η₂)) := by
  unfold HessianGeometry.divergence HessianGeometry.dualMap
  simp [hessianGeometry, logPartition, inner_sub_left, inner_sub_right, map_sub]
  have hcross : inner ℝ η₁ (G.sigma η₂) = inner ℝ η₂ (G.sigma η₁) := by
    calc
      inner ℝ η₁ (G.sigma η₂) = inner ℝ (G.sigma η₁) η₂ := by
        simpa using (G.sigma_symm.isSymmetric η₁ η₂).symm
      _ = inner ℝ η₂ (G.sigma η₁) := by simp [real_inner_comm]
  have hcross' : inner ℝ (G.sigma η₂) η₁ = inner ℝ η₂ (G.sigma η₁) := by
    calc
      inner ℝ (G.sigma η₂) η₁ = inner ℝ η₁ (G.sigma η₂) := by simp [real_inner_comm]
      _ = inner ℝ η₂ (G.sigma η₁) := hcross
  have hdiag : inner ℝ (G.sigma η₂) η₂ = inner ℝ η₂ (G.sigma η₂) := by
    simp [real_inner_comm]
  rw [hcross, hcross', hdiag]
  ring_nf

/-- 
Specialization: Softmax Attention over Gaussian keys.
The interaction score is proportional to the negative Mahalanobis distance.
This creates a "Gaussian Head" where aggregation is localized in embedding space.
-/
noncomputable def softmaxGaussianAttention
    {ι : Type _} [DecidableEq ι]
    (I : Finset ι) (hI : I.Nonempty) (keys : ι → E)
    (route : E → E → E) :
    (letI : BregmanDivergence E E := HessianGeometry.bregmanDiv G.hessianGeometry
     GeometricAttentionMap (bregmanTriadicCore (Q := E) (K := E) (V := E) route) ι) :=
  HessianGeometry.softmaxBregmanAttention G.hessianGeometry I hI keys route

end GaussianFamily

end InfoGeometry.ExponentialFamily.Gaussian
