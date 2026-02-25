import InfoGeometry.ExponentialFamily.Gaussian
import InfoGeometry.Research.KreinLadder
import InfoGeometry.Research.QuantumInference

namespace InfoGeometry.ExponentialFamily.GaussianLadder

open InfoGeometry.ExponentialFamily.Gaussian
open InfoGeometry.Research.KreinLadder
open InfoGeometry.Research.Drazin
open InfoGeometry.Research.SpectralInference
open InfoGeometry.Research.QuantumInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- 
Explicit Annihilation Operator for the Multivariate Gaussian Family.
Maps (x, θ) to (x, Σ x).
-/
noncomputable def gaussianAnnihilation (G : GaussianFamily E) : (DoubledSpace E) →ₗ[ℝ] (DoubledSpace E) :=
  { toFun := fun v => (v.1, G.sigma v.1)
    map_add' := by intro x y; simp
    map_smul' := by intro c x; simp }

/-- 
Explicit Creation Operator for the Multivariate Gaussian Family.
Maps (x, θ) to (x, - Σ x).
-/
noncomputable def gaussianCreation (G : GaussianFamily E) : (DoubledSpace E) →ₗ[ℝ] (DoubledSpace E) :=
  { toFun := fun v => (v.1, - G.sigma v.1)
    map_add' := by intro x y; simp [add_comm]
    map_smul' := by intro c x; simp }

omit [FiniteDimensional ℝ E] in
/--
Theorem: The Gaussian ladder operators satisfy the CCR with respect to the
Fisher Information metric (the covariance operator Σ).
[a, a_dag] applied to a state (x, θ) recovers the information flux.
-/
theorem gaussian_ccr (G : GaussianFamily E) (v : DoubledSpace E) :
    ((gaussianAnnihilation G) * (gaussianCreation G) - (gaussianCreation G) * (gaussianAnnihilation G)) v = 
    (0, 2 • G.sigma v.1) := by
  ext <;> simp [gaussianAnnihilation, gaussianCreation, two_smul, sub_eq_add_neg]

end InfoGeometry.ExponentialFamily.GaussianLadder
