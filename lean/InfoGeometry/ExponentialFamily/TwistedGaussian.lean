import InfoGeometry.ExponentialFamily.Gaussian
import InfoGeometry.Canonical.MoorePenrose
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace InfoGeometry.ExponentialFamily.TwistedGaussian

open InfoGeometry.Convex
open InfoGeometry.Canonical.MoorePenrose
open Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 
A Twisted Gaussian Family.
The precision/covariance operator Σ is perturbed by an anti-symmetric torsion operator T.
This models an inference system with 'memory' or 'twist' where updates do not commute.
-/
structure TwistedGaussianFamily (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] 
    extends GaussianFamily E where
  T : E →L[ℝ] E
  /-- The torsion operator is anti-symmetric. -/
  T_antisymm : ∀ u v : E, inner ℝ (T u) v = - inner ℝ u (T v)
  /-- Normality of `sigma + T` is equivalent to covariance-torsion commutation. -/
  normal_commutes : IsStarNormal (sigma + T) ↔ sigma * T = T * sigma

namespace TwistedGaussianFamily

variable (TG : TwistedGaussianFamily E)

/-- The total information operator A = Σ + T. -/
noncomputable def infoOperator : E →L[ℝ] E :=
  TG.sigma + TG.T

/-- Skew-adjointness of the torsion operator induced by anti-symmetry. -/
theorem adjoint_T_eq_neg : ContinuousLinearMap.adjoint TG.T = -TG.T := by
  ext y
  apply ext_inner_left ℝ
  intro v
  calc
    inner ℝ v ((ContinuousLinearMap.adjoint TG.T) y) = inner ℝ (TG.T v) y := by
      simpa using (ContinuousLinearMap.adjoint_inner_right TG.T v y)
    _ = - inner ℝ v (TG.T y) := TG.T_antisymm v y
    _ = inner ℝ v ((-TG.T) y) := by simp

/--
The adjoint of the information operator.
A† = Σ - T.
-/
theorem adjoint_infoOperator :
    ContinuousLinearMap.adjoint TG.infoOperator = TG.sigma - TG.T := by
  calc
    ContinuousLinearMap.adjoint TG.infoOperator
        = ContinuousLinearMap.adjoint TG.sigma + ContinuousLinearMap.adjoint TG.T := by
          simp [infoOperator]
    _ = TG.sigma + (-TG.T) := by
          simp [TG.sigma_symm.adjoint_eq, TG.adjoint_T_eq_neg]
    _ = TG.sigma - TG.T := by simp [sub_eq_add_neg]

/--
Bridge proposition for normality of Twisted Gaussians.
A Twisted Gaussian is 'Normal' (A * A† = A† * A) if and only if 
the torsion commutes with the covariance: [Σ, T] = 0.
-/
theorem normal_iff_commutes :
    IsStarNormal TG.infoOperator ↔ TG.sigma * TG.T = TG.T * TG.sigma :=
by simpa [infoOperator] using TG.normal_commutes

/--
The Explicit Chiral Scale for the Twisted Gaussian.
If the Drazin and Moore-Penrose projectors are computed for A = Σ + T, 
this function evaluates their anomaly magnitude.
-/
noncomputable def twistedChiralScale (A_D A_MP : E →L[ℝ] E) : ℝ :=
  chiralScale TG.infoOperator A_D A_MP

end TwistedGaussianFamily

end InfoGeometry.ExponentialFamily.TwistedGaussian
