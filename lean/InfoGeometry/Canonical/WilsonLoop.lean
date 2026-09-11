import InfoGeometry.Canonical.BeliefAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The operator-model Wilson loop is the complexified operator-norm readout. -/
@[simp] theorem wilsonLoopDiscrete_eq_norm
    (Dε : DiracField X E) (γ : List X) (dt : ℝ) :
    wilsonLoopDiscrete Dε γ dt =
      (‖wilsonPropagatorDiscrete Dε γ dt‖ : ℝ) := rfl

@[simp] theorem chiralPathWeight_eq_holonomy_mul_gibbs
    (H : HessianGeometry E) (Dε : DiracField (ℝ → E) E)
    (γ : ℝ → E) (N : ℕ) (T : ℝ) :
    chiralPathWeight H Dε γ N T
      = continuousWilsonLoop Dε γ
        * Complex.exp ((- (InfoGeometry.Canonical.SpectralInference.bayesianAction H
            (fun i => γ ((i : ℝ) / (N : ℝ))) N) : ℝ) / T) := rfl

@[simp] theorem expectedHolonomy_eq_partition_ratio
    (H : HessianGeometry E) (Dε : DiracField (ℝ → E) E)
    (paths : Finset (ℝ → E)) (N : ℕ) (T : ℝ) :
    expectedHolonomy H Dε paths N T
      = (∑ γ ∈ paths,
          continuousWilsonLoop Dε γ
            * Complex.exp ((- (InfoGeometry.Canonical.SpectralInference.bayesianAction H
                (fun i => γ ((i : ℝ) / (N : ℝ))) N) : ℝ) / T))
          / chiralPathIntegral H Dε paths N T := rfl

end InfoGeometry.Canonical.WilsonLoop
