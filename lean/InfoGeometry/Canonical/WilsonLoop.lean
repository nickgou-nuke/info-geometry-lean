import InfoGeometry.Canonical.BeliefAlgebra
import InfoGeometry.Canonical.GaussianHolonomy
import InfoGeometry.Canonical.PathIntegral
import InfoGeometry.Canonical.QuantumInference

/-!
# InfoGeometry.Canonical.WilsonLoop

Canonical façade/API surface for information Wilson loops, path integrals,
and belief-update noncommutativity. This file re-exports a curated user-facing
surface and provides canonical `[simp]` unfolding lemmas; it does not add new
bridge theorems of its own.
-/

namespace InfoGeometry.Canonical.WilsonLoop

export InfoGeometry.Canonical.QuantumInference (
  DiracField
  diracReg
  wilsonStep
  wilsonPropagatorDiscrete
  wilsonLoopDiscrete
  continuousWilsonLoop
)

export InfoGeometry.Canonical.PathIntegral (
  chiralPathWeight
  chiralPathIntegral
  expectedHolonomy
)

export InfoGeometry.Canonical.BeliefAlgebra (
  BeliefSystem
)

export InfoGeometry.Canonical.BeliefAlgebra.BeliefSystem (
  non_commutative_updates
  InformationLieAlgebra
)

export InfoGeometry.Canonical.GaussianHolonomy (
  gaussianDiracField
  gaussianWilsonLoopDiscrete
  gaussian_holonomy_flat
  gaussianDiracField_apply
  gaussianDiracField_const
)

open InfoGeometry.Canonical.QuantumInference
open InfoGeometry.Canonical.PathIntegral
open InfoGeometry.Convex
open scoped BigOperators

variable {X : Type*}
variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp] theorem wilsonLoopDiscrete_eq_det
    (Dε : DiracField X n) (γ : List X) (dt : ℂ) :
    wilsonLoopDiscrete Dε γ dt = Matrix.det (wilsonPropagatorDiscrete Dε γ dt) := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[simp] theorem chiralPathWeight_eq_holonomy_mul_gibbs
    (H : HessianGeometry E) (Dε : DiracField (ℝ → E) n) (γ : ℝ → E) (N : ℕ) (T : ℝ) :
    chiralPathWeight H Dε γ N T
      = continuousWilsonLoop Dε γ
        * Complex.exp ((- (InfoGeometry.Canonical.SpectralInference.bayesianAction H
            (fun i => γ ((i : ℝ) / (N : ℝ))) N) : ℝ) / T) := rfl

@[simp] theorem expectedHolonomy_eq_partition_ratio
    (H : HessianGeometry E) (Dε : DiracField (ℝ → E) n)
    (paths : Finset (ℝ → E)) (N : ℕ) (T : ℝ) :
    expectedHolonomy H Dε paths N T
      = (∑ γ ∈ paths,
          continuousWilsonLoop Dε γ
            * Complex.exp ((- (InfoGeometry.Canonical.SpectralInference.bayesianAction H
                (fun i => γ ((i : ℝ) / (N : ℝ))) N) : ℝ) / T))
          / chiralPathIntegral H Dε paths N T := rfl

end InfoGeometry.Canonical.WilsonLoop
