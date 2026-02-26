import InfoGeometry.Canonical.Promoted.SpectralInference
import InfoGeometry.Canonical.Promoted.QuantumInference
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace InfoGeometry.Research.PathIntegral

open InfoGeometry.Research.SpectralInference
open InfoGeometry.Research.QuantumInference
open InfoGeometry.Convex
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/--
The Chiral Path Weight for a Bayesian chain.
Incorporates both the classical inference cost (bayesianAction)
and the quantum-geometric holonomy (continuousWilsonLoop).
P(γ) ∝ tr(W[γ]) * exp(-S[γ] / T).
-/
noncomputable def chiralPathWeight (H : HessianGeometry E) (Dε : DiracField (ℝ → E) n) (γ : ℝ → E) (N : ℕ) (T : ℝ) : Complex :=
  let S := bayesianAction H (fun i => γ ((i : ℝ) / (N : ℝ))) N -- Discrete action sample
  let W := continuousWilsonLoop Dε γ
  W * (Complex.exp ((- S : ℝ) / T))

/--
The Chiral Path-Integral Partition Function Z.
Sums over the combined effects of information gain and manifold holonomy.
-/
noncomputable def chiralPathIntegral (H : HessianGeometry E) (Dε : DiracField (ℝ → E) n) (paths : Finset (ℝ → E)) (N : ℕ) (T : ℝ) : Complex :=
  ∑ γ ∈ paths, chiralPathWeight H Dε γ N T

/--
The Expected Holonomy ⟨W⟩.
Measures the average information rotation across all possible belief trajectories.
This identifies the global 'Learning Phase' of the system.
-/
noncomputable def expectedHolonomy (H : HessianGeometry E) (Dε : DiracField (ℝ → E) n) (paths : Finset (ℝ → E)) (N : ℕ) (T : ℝ) : Complex :=
  (∑ γ ∈ paths, (continuousWilsonLoop Dε γ) * (Complex.exp ((- (bayesianAction H (fun i => γ ((i : ℝ) / (N : ℝ))) N) : ℝ) / T))) / (chiralPathIntegral H Dε paths N T)

end InfoGeometry.Research.PathIntegral
