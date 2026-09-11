import InfoGeometry.ExponentialFamily.Gaussian
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KreinLadder
import InfoGeometry.Canonical.QuantumInference

namespace InfoGeometry.ExponentialFamily.GaussianLadder

open InfoGeometry.ExponentialFamily.Gaussian
open InfoGeometry.Krein
open InfoGeometry.Canonical.KreinLadder
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.QuantumInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Explicit Annihilation Operator for the Multivariate Gaussian Family.
Maps (x, θ) to (x, Σ x).
-/
noncomputable def gaussianAnnihilation (G : GaussianFamily E) :
    (InfoGeometry.Canonical.KreinLadder.DoubledSpace E) →ₗ[ℝ]
      (InfoGeometry.Canonical.KreinLadder.DoubledSpace E) :=
  { toFun := fun v => to_doubled (WithLp.fst v) (G.sigma (WithLp.fst v))
    map_add' := by
      intro x y
      apply (WithLp.ofLp_injective 2)
      simp [to_doubled, map_add]
    map_smul' := by
      intro c x
      apply (WithLp.ofLp_injective 2)
      simp [to_doubled, map_smul] }

/--
Explicit Creation Operator for the Multivariate Gaussian Family.
Maps (x, θ) to (x, - Σ x).
-/
noncomputable def gaussianCreation (G : GaussianFamily E) :
    (InfoGeometry.Canonical.KreinLadder.DoubledSpace E) →ₗ[ℝ]
      (InfoGeometry.Canonical.KreinLadder.DoubledSpace E) :=
  { toFun := fun v => to_doubled (WithLp.fst v) (- G.sigma (WithLp.fst v))
    map_add' := by
      intro x y
      apply (WithLp.ofLp_injective 2)
      simp [to_doubled, map_add, add_comm]
    map_smul' := by
      intro c x
      apply (WithLp.ofLp_injective 2)
      simp [to_doubled, map_smul, smul_neg] }

omit [FiniteDimensional ℝ E] in
/--
Theorem: The Gaussian ladder operators satisfy the CCR with respect to the
Fisher Information metric (the covariance operator Σ).
[a, a_dag] applied to a state (x, θ) recovers the information flux.
-/
theorem gaussian_ccr (G : GaussianFamily E)
    (v : InfoGeometry.Canonical.KreinLadder.DoubledSpace E) :
    ((gaussianAnnihilation G).comp (gaussianCreation G)
      - (gaussianCreation G).comp (gaussianAnnihilation G)) v =
    to_doubled 0 (2 • G.sigma (WithLp.fst v)) := by
  apply (WithLp.ofLp_injective 2)
  ext <;> simp [gaussianAnnihilation, gaussianCreation, to_doubled, two_smul]

end InfoGeometry.ExponentialFamily.GaussianLadder
