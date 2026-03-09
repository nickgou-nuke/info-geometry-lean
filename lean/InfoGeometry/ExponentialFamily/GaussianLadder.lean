import InfoGeometry.ExponentialFamily.Gaussian
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
  { toFun := fun v => toDoubled (DoubledSpace.fst v) (G.sigma (DoubledSpace.fst v))
    map_add' := by intro x y; sorry
    map_smul' := by intro c x; sorry }

/--
Explicit Creation Operator for the Multivariate Gaussian Family.
Maps (x, θ) to (x, - Σ x).
-/
noncomputable def gaussianCreation (G : GaussianFamily E) :
    (InfoGeometry.Canonical.KreinLadder.DoubledSpace E) →ₗ[ℝ]
      (InfoGeometry.Canonical.KreinLadder.DoubledSpace E) :=
  { toFun := fun v => toDoubled (DoubledSpace.fst v) (- G.sigma (DoubledSpace.fst v))
    map_add' := by intro x y; sorry
    map_smul' := by intro c x; sorry }

omit [FiniteDimensional ℝ E] in
/--
Theorem: The Gaussian ladder operators satisfy the CCR with respect to the
Fisher Information metric (the covariance operator Σ).
[a, a_dag] applied to a state (x, θ) recovers the information flux.
-/
theorem gaussian_ccr (G : GaussianFamily E)
    (v : InfoGeometry.Canonical.KreinLadder.DoubledSpace E) :
    ((gaussianAnnihilation G) * (gaussianCreation G) - (gaussianCreation G) * (gaussianAnnihilation G)) v =
    toDoubled 0 (2 • G.sigma (DoubledSpace.fst v)) := by
  sorry

end InfoGeometry.ExponentialFamily.GaussianLadder
