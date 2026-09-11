import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QuantumInference
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace InfoGeometry.Canonical.PathIntegral

open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.QuantumInference
open InfoGeometry.Convex
open scoped BigOperators

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Chiral Path Weight for a Bayesian chain.
Incorporates both the classical inference cost (bayesianAction)
and the quantum-geometric holonomy (continuousWilsonLoop).
P(γ) ∝ tr(W[γ]) * exp(-S[γ] / T).
-/
noncomputable def chiralPathWeight
    (H : HessianGeometry E) (Dε : DiracField (ℝ → E) E)
    (γ : ℝ → E) (N : ℕ) (T : ℝ) : Complex :=
  let S := bayesianAction H (fun i => γ ((i : ℝ) / (N : ℝ))) N -- Discrete action sample
  let W := continuousWilsonLoop Dε γ
  W * (Complex.exp ((- S : ℝ) / T))

/--
The Chiral Path-Integral Partition Function Z.
Sums over the combined effects of information gain and manifold holonomy.
-/
noncomputable def chiralPathIntegral
    (H : HessianGeometry E) (Dε : DiracField (ℝ → E) E)
    (paths : Finset (ℝ → E)) (N : ℕ) (T : ℝ) : Complex :=
  ∑ γ ∈ paths, chiralPathWeight H Dε γ N T

/--
The Expected Holonomy ⟨W⟩.
Measures the average information rotation across all possible belief trajectories.
This identifies the global 'Learning Phase' of the system.
-/
noncomputable def expectedHolonomy
    (H : HessianGeometry E) (Dε : DiracField (ℝ → E) E)
    (paths : Finset (ℝ → E)) (N : ℕ) (T : ℝ) : Complex :=
  (∑ γ ∈ paths, (continuousWilsonLoop Dε γ) * (Complex.exp ((- (bayesianAction H (fun i => γ ((i : ℝ) / (N : ℝ))) N) : ℝ) / T))) / (chiralPathIntegral H Dε paths N T)

end InfoGeometry.Canonical.PathIntegral
